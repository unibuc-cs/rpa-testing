# THis is the main workflow  parser purpose script that coordinates all other components to do parsing and retrieve a Workflow Graph object

import json
import sys
import pickle
import os
from Parser_WorkflowExpressions import *
from Executor_NodesExec import *
from WorkflowGraph import *
import re

class WorkflowParser:
    def __init__(self, astFuzzerNodeExecutor : ASTFuzzerNodeExecutor,
                        workflowExpressionParser : WorkflowExpressionsParser):
        self.astFuzzerNodeExecutor = astFuzzerNodeExecutor
        self.workflowExpressionParser = workflowExpressionParser

    def parseVariable(self, workflowName : str, varName : str, varData):

        varType = varData["Type"]
        defaultValue = varData.get("Default")

        # Declare a variable and execute it in the executor
        # This will also put it in the datastore inside executor and make all connection links
        varDecl = ASTFuzzerNode_VariableDecl(varName=workflowName+ ":"+varName, typeName=varType, defaultValue=defaultValue)
        self.astFuzzerNodeExecutor.executeNode(varDecl)

    def parseWorkflows(self, inputPath : str, baseOutPath : str) -> WorkflowGraph:
        workflowGraph : WorkflowGraph = WorkflowGraph(dataStore=self.astFuzzerNodeExecutor.DS)

        with open(inputPath) as json_file:
            dataAll = json.load(json_file)

            workflowsDataSpec = dataAll['workflows']
            graph = dataAll['graph']
            startNode = dataAll['startNode']
            startGraph = startNode.split(":")
            assert len(startGraph) > 0
            workflowGraph.setMainWorkflowName(startGraph[0])
            workflowGraph.entryTestNodeId = startNode

            workflowGraph.debugColors = {}
            nodeIdToInstance: Dict[str, SymGraphNodeBranch] = {}

            # Step 0: Create the variables, check all existing workflows, create debug colors and append to the variables dictionary each individual workflow used
            for workflowData in workflowsDataSpec:
                variables = workflowData['variables']
                graphName = workflowData['displayName']
                invokedBy = workflowData["invokedBy"]
                startNode = workflowData["startNode"]
                workflowGraph.debugColors[graphName] = getDebugColorByName(graphName)

                # Parse each variable
                for varName, varData in variables.items():
                    self.parseVariable(workflowName = graphName, varName=varName, varData=varData)

            # Step 1: Create all the node firsts and cache the inverse dictionary in the graph from node_id to node instance
            for nodeFullName, nodeData in graph.items():
                nodeFullNameSplit = nodeFullName.split(":")
                assert len(nodeFullNameSplit) ==2, f"Node content is {nodeFullNameSplit}. Expecting format namespace:nodeName"
                parentGraphName = nodeFullNameSplit[0]
                nodeName = nodeFullNameSplit[1]

                ## DEBUG CODE
                if "For_Each_Row_in_Data_Table_3" in nodeFullName:
                    a = 3
                    a += 1

                # Parse node expr
                expression_raw_str = nodeData.get('expression')
                expression_node = None
                if expression_raw_str != "" and expression_raw_str != None:
                    expression_node = self.workflowExpressionParser.parseModuleCodeBlock(expression_raw_str)[0]

                # Create a node based on its expression node
                nodeInst = None
                if expression_node is None or not expression_node.type in [ASTFuzzerNodeType.COMPARE, ASTFuzzerNodeType.LOGIC_OP_BINARY, ASTFuzzerNodeType.FOREACH_ITERATION]:
                    nodeInst = SymGraphNodeFlow(id=nodeFullName)
                else:
                    nodeInst = SymGraphNodeBranch(id=nodeFullName)
                nodeInst.expression = expression_node
                nodeInst.expression_rawStr = expression_raw_str

                # Register the new node in the local map
                nodeIdToInstance[nodeFullName] = nodeInst

                # Fill in the debug info stuff for this node
                #-----------------------
                # See here all the graphiviz attributes: https://graphviz.org/doc/info/attrs.html
                node_shape = None
                if nodeInst.id == workflowGraph.entryTestNodeId:
                    node_shape = 'doubleoctagon'
                elif nodeInst.nodeType == NodeTypes.BRANCH_NODE:
                    node_shape = 'diamond'
                else:
                    node_shape = 'box'

                # 'square' if nodeInst.nodeType == NodeTypes.BranchNode else 'circle'
                nodeGraphParentName = nodeInst.getGraphNameFromNodeId()
                assert nodeGraphParentName in workflowGraph.debugColors, f"Looking for graph named {nodeGraphParentName} but it doesn't exist "
                node_color = workflowGraph.debugColors[nodeGraphParentName]
                node_fill_color = 'blue' if nodeInst.id == workflowGraph.entryTestNodeId else 'white'
                node_style = 'filled'

                labelStr = nodeInst.getDebugLabel()
                # HTML way ...maybe later
                # labelStr = f"<{nodeInst.id}<BR/><FONT POINT-SIZE=\"10\">v[add]  $#60 100 </FONT>>"
                # 'square' if nodeInst.nodeType == NodeTypes.BranchNode else 'circle'
                nodeGraphParentName = nodeInst.getGraphNameFromNodeId()
                assert nodeGraphParentName in workflowGraph.debugColors, f"Looking for graph named {nodeGraphParentName} but it doesn't exist "
                node_color = workflowGraph.debugColors[nodeGraphParentName]
                node_fill_color = 'blue' if nodeInst.id == workflowGraph.entryTestNodeId else 'white'
                node_style = 'filled'

                #-----------------
                # HTML way ...maybe later
                # labelStr = f"<{nodeInst.id}<BR/><FONT POINT-SIZE=\"10\">v[add]  $#60 100 </FONT>>"

                workflowGraph.graphInst.add_node(nodeInst, label=labelStr, shape=node_shape,
                                       color=node_color, fillcolor=node_fill_color,
                                        style=node_style)

            workflowGraph.graphInst.graph['nodeIdToInstance'] = nodeIdToInstance

            # Step 2: Create the links inside the nodes and graph
            for nodeFullName, nodeData in graph.items():
                parentNodeInst = nodeIdToInstance[nodeFullName]
                transitions = nodeData.get('transitions')

                if parentNodeInst.nodeType == NodeTypes.BRANCH_NODE:
                    # Currently we support two transition on branching nodes, T and F.
                    # Later add support for switch, etc
                    # Technically, this limitation is only on parsing side, as you can see the graph instance support generic transitions !
                    assert len(transitions) == 2
                    for trans in transitions:
                        assert "value" in trans and trans["value"] in ["True", "False"], "Sanity input check failed !"
                        trans_branchValue = trans["value"]
                        trans_branchDest_nodeId = trans["destination"]
                        trans_branchDest_nodeInst = nodeIdToInstance[trans_branchDest_nodeId]
                        edgeLabel: str = 'T' if trans_branchValue == 'True' else 'F'

                        # Add the edge into the graph instance
                        workflowGraph.graphInst.add_edge(parentNodeInst, trans_branchDest_nodeInst, label=edgeLabel, labelfontsize=20)

                elif parentNodeInst.nodeType == NodeTypes.FLOW_NODE:
                    if len(transitions) > 0:
                        assert len(transitions) == 1 and transitions[0]["value"] == "True", "This is the kind of input we expect for a flow transition node (not sink)"
                        trans = transitions[0]
                        trans_branchDest_nodeId = trans["destination"]
                        trans_branchDest_nodeInst = nodeIdToInstance[trans_branchDest_nodeId]

                        # Add the edge into the graph instance
                        workflowGraph.graphInst.add_edge(parentNodeInst, trans_branchDest_nodeInst)

        return workflowGraph


