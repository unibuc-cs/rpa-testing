def customizeAssignActivity(referenceID, activityID, variableName, value):
        template = f"""
        <FlowStep x:Name="__ReferenceID{referenceID}">
        <sap:WorkflowViewStateService.ViewState>
        <scg:Dictionary x:TypeArguments="x:String, x:Object">
        <av:Point x:Key="ShapeLocation">348.8,250</av:Point>
        <av:Size x:Key="ShapeSize">262.4,60</av:Size>
        </scg:Dictionary>
        </sap:WorkflowViewStateService.ViewState>
        <Assign DisplayName="Automatically Inserted" sap:VirtualizedContainerService.HintSize="262.4,60" sap2010:WorkflowViewState.IdRef="Assign_{activityID}">
        <Assign.To>
        <OutArgument x:TypeArguments="x:String">[{variableName}]</OutArgument>
        </Assign.To>
        <Assign.Value>
        <InArgument x:TypeArguments="x:String">{value}</InArgument>
        </Assign.Value>
        <sap:WorkflowViewStateService.ViewState>
        <scg:Dictionary x:TypeArguments="x:String, x:Object">
        <x:Boolean x:Key="IsExpanded">True</x:Boolean>
        </scg:Dictionary>
        </sap:WorkflowViewStateService.ViewState>
        </Assign>
        <FlowStep.Next>
        """

        templateByLines = [i.strip() for i in template.splitlines() if i.strip() != ""]

        return templateByLines