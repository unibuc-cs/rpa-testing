using System;
using System.Activities;
using System.Activities.Statements;
using System.Collections.Generic;
using XMLParsing.Common;
using XMLParsing.Services.Parsers.ActivityParser;
using XMLParsing.Utils;

/*
    State machines can have no end, so there are chances that the final node is null.

    TODO: What to do with triggers?
 */

namespace XMLParsing.Services
{
    class StateMachineActivityParser : DefaultActivityParser
    {
        public override Tuple<Node, Node> ParseImplementation(Activity activity, Graph graph, WorkflowData workflowData)
        {
            NativeActivity nativeActivity = activity as NativeActivity;
            if(nativeActivity == null || ! nativeActivity.GetType().Equals(typeof(StateMachine)))
            {
                throw new XamlParserException("Unexpected type of activity");
            }

            StateMachine stateMachine = nativeActivity as StateMachine;

            // Parse variables
            ExtractVariables(stateMachine, workflowData);

            return ParseNodeStructure(stateMachine, graph, workflowData);
        }

        private void ExtractVariables(StateMachine stateMachine, WorkflowData workflowData)
        {
            foreach (var variable in stateMachine.Variables)
            {
                workflowData.Variables.Add(variable);
            }
        }

        private void ExtractVariables(State state, WorkflowData workflowData)
        {
            foreach (var variable in state.Variables)
            {
                workflowData.Variables.Add(variable);
            }
        }

        private Tuple<Node, Node> ParseNodeStructure(StateMachine stateMachine, Graph graph, WorkflowData workflowData)
        {
            Dictionary<State, Tuple<Node, Node>> nodes = new Dictionary<State, Tuple<Node, Node>>();

            // Parse the states
            foreach (var state in stateMachine.States)
            {
                var stateEnds = ParseState(state, graph, workflowData);
                nodes[state] = stateEnds;
            }

            // Parse the transitions
            foreach (var state in stateMachine.States)
            {
                ParseTransitions(state, graph, workflowData, nodes);
            }

            var startNode = nodes[stateMachine.InitialState].Item1;
            var finalNode = GetFinalNode(stateMachine, graph, workflowData, nodes);

            return Tuple.Create<Node, Node>(startNode, finalNode);
        }

        private Node GetFinalNode(StateMachine stateMachine, Graph graph, WorkflowData workflowData, Dictionary<State, Tuple<Node, Node>> nodes)
        {
            // We may or may not have a final node. 
            // Let's first get a collection of final nodes;
            IList<Node> finalNodes = new List<Node>();
            foreach(var state in stateMachine.States)
            {
                if (state.IsFinal == false)
                {
                    continue;
                }

                finalNodes.Add(nodes[state].Item2);
            }

            if(finalNodes.Count == 0)
            {
                // We have no final state -> no need for a converging virtual node;
                return null;
            }

            Node endNode = ActivityUtils.CreateEmptyNode(workflowData.DisplayName);
            endNode.DisplayName = nodes[stateMachine.InitialState].Item1.DisplayName + "_Virtual_End";
            graph.Nodes.Add(endNode);

            foreach (var finalNode in finalNodes)
            {
                Common.Transition t = new Common.Transition();
                t.Source = finalNode;
                t.Destination = endNode;
                t.Expression = "";
                t.ExpressionValue = Common.Transition.TRUE_TRANSITION_VALUE;
                graph.Transitions.Add(t);
            }

            return endNode;
        }

        private void ParseTransitions(State state, Graph graph, WorkflowData workflowData, Dictionary<State, Tuple<Node, Node>> nodes)
        {
            var lastNodeToBind = nodes[state].Item2;

            foreach (var transition in state.Transitions)
            {
                Activity transitionAction = transition.Action;
                Tuple<Node, Node> transitionActionEnds = null;
                if (transitionAction != null)
                {
                    IActivityParser activityParser = ActivityParserFactory.Instance.GetParser(transitionAction);
                    transitionActionEnds = activityParser.ParseActivity(transitionAction, graph, workflowData);
                }

                var expressionText = ExpressionUtils.TryParseExpression(transition.Condition);
                Node transitionNode = ActivityUtils.CreateSimpleNodeFromTransition(transition, workflowData.DisplayName);
                transitionNode.Expression = expressionText;
                transitionNode.IsConditional = true;
                graph.Nodes.Add(transitionNode);

                // Bind to the last node - exception case if it is the first node bound
                if (lastNodeToBind == nodes[state].Item2)
                {
                    Common.Transition t = new Common.Transition();
                    t.Source = lastNodeToBind;
                    t.Destination = transitionNode;
                    t.Expression = "";
                    t.ExpressionValue = Common.Transition.TRUE_TRANSITION_VALUE;
                    graph.Transitions.Add(t);
                }
                else
                {
                    Common.Transition t = new Common.Transition();
                    t.Source = lastNodeToBind;
                    t.Destination = transitionNode;
                    t.Expression = lastNodeToBind.Expression;
                    t.ExpressionValue = Common.Transition.FALSE_TRANSITION_VALUE;
                    graph.Transitions.Add(t);
                }

                // Bind to transition action if exists or directly to the destination node
                if (transitionActionEnds != null)
                {
                    Common.Transition t1 = new Common.Transition();
                    t1.Source = transitionNode;
                    t1.Destination = transitionActionEnds.Item1;
                    t1.Expression = transitionNode.Expression;
                    t1.ExpressionValue = Common.Transition.TRUE_TRANSITION_VALUE;
                    graph.Transitions.Add(t1);

                    Common.Transition t2 = new Common.Transition();
                    t2.Source = transitionActionEnds.Item2;
                    t2.Destination = nodes[transition.To].Item1;
                    t2.Expression = "";
                    t2.ExpressionValue = Common.Transition.TRUE_TRANSITION_VALUE;
                    graph.Transitions.Add(t2);
                } 
                else
                {
                    Common.Transition t = new Common.Transition();
                    t.Source = transitionNode;
                    t.Destination = nodes[transition.To].Item1;
                    t.Expression = lastNodeToBind.Expression;
                    t.ExpressionValue = Common.Transition.TRUE_TRANSITION_VALUE;
                    graph.Transitions.Add(t);
                }

                lastNodeToBind = transitionNode;
            }
        }

        private Tuple<Node, Node> ParseState(State state, Graph graph, WorkflowData workflowData)
        {
            ExtractVariables(state, workflowData);

            Node startNode = ActivityUtils.CreateSimpleNodeFromState(state, workflowData.DisplayName);
            graph.Nodes.Add(startNode);

            Node endNode = ActivityUtils.CreateEmptyNode(workflowData.DisplayName);
            endNode.DisplayName = startNode.DisplayName + "_Virtual_State_End";
            graph.Nodes.Add(endNode);

            Activity stateEntry = state.Entry;
            Tuple<Node, Node> entryActivityEnds = null;
            if (stateEntry != null)
            {
                IActivityParser activityParser = ActivityParserFactory.Instance.GetParser(stateEntry);
                entryActivityEnds = activityParser.ParseActivity(stateEntry, graph, workflowData);
            }

            Activity stateExit = state.Exit;
            Tuple<Node, Node> exitActivityEnds = null;
            if (stateExit != null)
            {
                IActivityParser activityParser = ActivityParserFactory.Instance.GetParser(stateExit);
                exitActivityEnds = activityParser.ParseActivity(stateExit, graph, workflowData);
            }

            /// Connect the states
            Action<Node, Node> createsimpleTransition = (source, destination) =>
            {
                Common.Transition t = new Common.Transition();
                t.Source = source;
                t.Destination = destination;
                t.Expression = "";
                t.ExpressionValue = Common.Transition.TRUE_TRANSITION_VALUE;
                graph.Transitions.Add(t);
            };

            if (stateEntry != null)
            {
                createsimpleTransition(startNode, entryActivityEnds.Item1);
                if (stateExit != null)
                {
                    createsimpleTransition(entryActivityEnds.Item2, exitActivityEnds.Item1);
                    createsimpleTransition(exitActivityEnds.Item2, endNode);
                } 
                else
                {
                    createsimpleTransition(entryActivityEnds.Item2, endNode);
                }
            }
            else
            {
                if (stateExit != null)
                {
                    createsimpleTransition(startNode, exitActivityEnds.Item1);
                    createsimpleTransition(exitActivityEnds.Item2, endNode);
                }
                else
                {
                    createsimpleTransition(startNode, endNode);
                }
            }

            return Tuple.Create (startNode, endNode);
        }


    }
}
