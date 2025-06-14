def generate_flowchart_with_condition(activity_name, loan, term):
    file_content = f"""
    <Activity mc:Ignorable="sap sap2010" x:Class="{activity_name}" mva:VisualBasic.Settings="{{x:Null}}" sap2010:WorkflowViewState.IdRef="Flowchart_1"
    xmlns="http://schemas.microsoft.com/netfx/2009/xaml/activities" 
    xmlns:av="http://schemas.microsoft.com/winfx/2006/xaml/presentation" 
    xmlns:mc="http://schemas.openxmlformats.org/markup-compatibility/2006" 
    xmlns:mva="clr-namespace:Microsoft.VisualBasic.Activities;assembly=System.Activities" 
    xmlns:sap="http://schemas.microsoft.com/netfx/2009/xaml/activities/presentation" 
    xmlns:sap2010="http://schemas.microsoft.com/netfx/2010/xaml/activities/presentation" 
    xmlns:sco="clr-namespace:System.Collections.ObjectModel;assembly=mscorlib" 
    xmlns:x="http://schemas.microsoft.com/winfx/2006/xaml">
        <TextExpression.NamespacesForImplementation>
            <sco:Collection x:TypeArguments="x:String">
                <x:String>System.Activities</x:String>
                <x:String>System.Activities.Statements</x:String>
                <x:String>System.Activities.Expressions</x:String>
                <x:String>System.Activities.Validation</x:String>
                <x:String>System.Activities.XamlIntegration</x:String>
                <x:String>Microsoft.VisualBasic</x:String>
                <x:String>Microsoft.VisualBasic.Activities</x:String>
                <x:String>System</x:String>
                <x:String>System.Collections</x:String>
                <x:String>System.Collections.Generic</x:String>
                <x:String>System.Data</x:String>
                <x:String>System.Diagnostics</x:String>
                <x:String>System.Drawing</x:String>
                <x:String>System.IO</x:String>
                <x:String>System.Linq</x:String>
                <x:String>System.Net.Mail</x:String>
                <x:String>System.Xml</x:String>
                <x:String>System.Xml.Linq</x:String>
                <x:String>UiPath.Core</x:String>
                <x:String>UiPath.Core.Activities</x:String>
            </sco:Collection>
        </TextExpression.NamespacesForImplementation>
        <TextExpression.ReferencesForImplementation>
            <sco:Collection x:TypeArguments="AssemblyReference">
                <AssemblyReference>System.Activities</AssemblyReference>
                <AssemblyReference>Microsoft.VisualBasic</AssemblyReference>
                <AssemblyReference>mscorlib</AssemblyReference>
                <AssemblyReference>System.Data</AssemblyReference>
                <AssemblyReference>System</AssemblyReference>
                <AssemblyReference>System.Drawing</AssemblyReference>
                <AssemblyReference>System.Core</AssemblyReference>
                <AssemblyReference>System.Xml</AssemblyReference>
                <AssemblyReference>System.Xml.Linq</AssemblyReference>
                <AssemblyReference>PresentationFramework</AssemblyReference>
                <AssemblyReference>WindowsBase</AssemblyReference>
                <AssemblyReference>PresentationCore</AssemblyReference>
                <AssemblyReference>System.Xaml</AssemblyReference>
                <AssemblyReference>UiPath.System.Activities</AssemblyReference>
                <AssemblyReference>UiPath.UiAutomation.Activities</AssemblyReference>
            </sco:Collection>
        </TextExpression.ReferencesForImplementation>
        <Flowchart DisplayName="Flowchart" sap2010:WorkflowViewState.IdRef="Flowchart_1">
            <sap:WorkflowViewStateService.ViewState>
                <scg:Dictionary x:TypeArguments="x:String, x:Object">
                    <x:Boolean x:Key="IsExpanded">False</x:Boolean>
                    <av:Point x:Key="ShapeLocation">270,2.5</av:Point>
                    <av:Size x:Key="ShapeSize">60,75.2</av:Size>
                </scg:Dictionary>
            </sap:WorkflowViewStateService.ViewState>
            <Flowchart.StartNode>
                <x:Null />
            </Flowchart.StartNode>
            <FlowDecision DisplayName="Flow Decision" sap2010:WorkflowViewState.IdRef="FlowDecision_1">
                <sap:WorkflowViewStateService.ViewState>
                    <scg:Dictionary x:TypeArguments="x:String, x:Object">
                        <x:Boolean x:Key="IsExpanded">True</x:Boolean>
                    </scg:Dictionary>
                </sap:WorkflowViewStateService.ViewState>
                <FlowDecision.Condition>
                    <InArgument x:TypeArguments="x:Boolean">{loan} &lt; 1000</InArgument>
                </FlowDecision.Condition>
                <FlowDecision.True>
                    <Sequence DisplayName="True Sequence" sap2010:WorkflowViewState.IdRef="Sequence_2">
                        <!-- Add activities for true branch here -->
                    </Sequence>
                </FlowDecision.True>
                <FlowDecision.False>
                    <Sequence DisplayName="False Sequence" sap2010:WorkflowViewState.IdRef="Sequence_3">
                        <!-- Add activities for false branch here -->
                    </Sequence>
                </FlowDecision.False>
            </FlowDecision>
        </Flowchart>
    </Activity>
    """
    file_content = file_content.replace('\n', '')

    # Remove extra spaces
    file_content = ' '.join(file_content.split())
    return file_content
