class Activities:
    def __init__(self, activities_data):
        self.activities_data = activities_data

    def generate_flowchart_pin(self, local_number_retries,local_pin_test,expected_pin,actual_pin_values,out_pin_check_successful):
        file_content = f"""
            <Activity mc:Ignorable="sap sap2010" x:Class="Pin" xmlns="http://schemas.microsoft.com/netfx/2009/xaml/activities" xmlns:av="http://schemas.microsoft.com/winfx/2006/xaml/presentation" xmlns:mc="http://schemas.openxmlformats.org/markup-compatibility/2006" xmlns:mca="clr-namespace:Microsoft.CSharp.Activities;assembly=System.Activities" xmlns:s="clr-namespace:System;assembly=mscorlib" xmlns:sap="http://schemas.microsoft.com/netfx/2009/xaml/activities/presentation" xmlns:sap2010="http://schemas.microsoft.com/netfx/2010/xaml/activities/presentation" xmlns:scg="clr-namespace:System.Collections.Generic;assembly=mscorlib" xmlns:sco="clr-namespace:System.Collections.ObjectModel;assembly=mscorlib" xmlns:sd="clr-namespace:System.Data;assembly=System.Data" xmlns:ui="http://schemas.uipath.com/workflow/activities" xmlns:x="http://schemas.microsoft.com/winfx/2006/xaml">
              <x:Members>
                <x:Property Name="out_pin_check_successful" Type="OutArgument(x:Boolean)" />
              </x:Members>
              <sap2010:ExpressionActivityEditor.ExpressionActivityEditor>C#</sap2010:ExpressionActivityEditor.ExpressionActivityEditor>
              <sap:VirtualizedContainerService.HintSize>1134,1342.4</sap:VirtualizedContainerService.HintSize>
              <sap2010:WorkflowViewState.IdRef>ActivityBuilder_1</sap2010:WorkflowViewState.IdRef>
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
                  <x:String>System.Text</x:String>
                  <x:String>System.Xml.Linq</x:String>
                  <x:String>UiPath.Core</x:String>
                  <x:String>UiPath.Core.Activities</x:String>
                  <x:String>System.Windows.Markup</x:String>
                  <x:String>System.ComponentModel</x:String>
                  <x:String>System.Runtime.Serialization</x:String>
                  <x:String>System.Xml.Serialization</x:String>
                  <x:String>System.Collections.ObjectModel</x:String>
                  <x:String>UiPath.CSV</x:String>
                  <x:String>System.Activities.DynamicUpdate</x:String>
                  <x:String>UiPath.CSV.Activities</x:String>
                  <x:String>System.Linq.Expressions</x:String>
                </sco:Collection>
              </TextExpression.NamespacesForImplementation>
              <TextExpression.ReferencesForImplementation>
                <sco:Collection x:TypeArguments="AssemblyReference">
                  <AssemblyReference>Microsoft.CSharp</AssemblyReference>
                  <AssemblyReference>System</AssemblyReference>
                  <AssemblyReference>System.Core</AssemblyReference>
                  <AssemblyReference>System.Activities</AssemblyReference>
                  <AssemblyReference>System.Data</AssemblyReference>
                  <AssemblyReference>System.Runtime.Serialization</AssemblyReference>
                  <AssemblyReference>System.ServiceModel</AssemblyReference>
                  <AssemblyReference>System.ServiceModel.Activities</AssemblyReference>
                  <AssemblyReference>System.Xaml</AssemblyReference>
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
                  <AssemblyReference>UiPath.Excel</AssemblyReference>
                  <AssemblyReference>UiPath.Excel.Activities</AssemblyReference>
                  <AssemblyReference>Microsoft.Bcl.AsyncInterfaces</AssemblyReference>
                  <AssemblyReference>System.ValueTuple</AssemblyReference>
                  <AssemblyReference>System.ComponentModel.Composition</AssemblyReference>
                  <AssemblyReference>UiPath.Mail</AssemblyReference>
                  <AssemblyReference>System.Memory</AssemblyReference>
                  <AssemblyReference>UiPath.OCR.Activities.Design</AssemblyReference>
                  <AssemblyReference>UiPath.UIAutomationCore</AssemblyReference>
                  <AssemblyReference>System.Data.DataSetExtensions</AssemblyReference>
                </sco:Collection>
              </TextExpression.ReferencesForImplementation>
              <Flowchart sap2010:Annotation.AnnotationText="Workflow is meant to check if the robot that is executing can provide a valid pin for the bank account. There is a retry mechanism and, for now, everything is hardcoded. &#xA;expected_pin = &quot;1234&quot;&#xA;actual_pin_values = [&quot;1235&quot;, &quot;1324&quot;, &quot;1234&quot;]&#xA;&#xA;Variable annotation restrictions: &#xA;- should start with `@Variables`&#xA;- should be followed by a json object&#xA;- should be last in annotation text&#xA;&#xA;@Variables&#xA;{{& quot;local_number_retries & quot;:{{& quot;min & quot;:0,&quot;max&quot;:3}},&quot;local_test_data_expected&quot;:{{& quot;path & quot;:&quot;pin_mocked_data.csv&quot;}},&quot;local_test_data_actual&quot;:{{& quot;path & quot;:&quot;pin_real_data.csv&quot;}},&quot;actual_pin_values&quot;:{{& quot;bounds & quot;:10,&quot;min&quot;:1111,&quot;max&quot;:9999,&quot;userInput&quot; : &quot;True&quot;}}" DisplayName="Pin" sap:VirtualizedContainerService.HintSize="754.4,1177.2" sap2010:WorkflowViewState.IdRef="Flowchart_1">
                <Flowchart.Variables>
                  <Variable x:TypeArguments="x:Int32" sap2010:Annotation.AnnotationText="Number of retries given as static input - for now it's not defined -&gt; infinite loop" Default="0" Name="local_number_retries" />
                  <Variable x:TypeArguments="x:Boolean" Name="local_pin_test" />
                  <Variable x:TypeArguments="x:Int32" Name="expected_pin" />
                  <Variable x:TypeArguments="s:Int32[]" Name="actual_pin_values" />
                </Flowchart.Variables>
                <sap:WorkflowViewStateService.ViewState>
                  <scg:Dictionary x:TypeArguments="x:String, x:Object">
                    <x:Boolean x:Key="IsExpanded">True</x:Boolean>
                    <av:Point x:Key="ShapeLocation">40,2.4</av:Point>
                    <av:Size x:Key="ShapeSize">60,75.2</av:Size>
                    <x:Double x:Key="Width">720.30585235907688</x:Double>
                    <av:PointCollection x:Key="ConnectorLocation">100,39.9 190,39.9 190,87</av:PointCollection>
                    <x:Double x:Key="Height">915.8</x:Double>
                    <x:Boolean x:Key="IsAnnotationDocked">True</x:Boolean>
                  </scg:Dictionary>
                </sap:WorkflowViewStateService.ViewState>
                <Flowchart.StartNode>
                  <x:Reference>__ReferenceID8</x:Reference>
                </Flowchart.StartNode>
                <FlowStep x:Name="__ReferenceID2">
                  <sap:WorkflowViewStateService.ViewState>
                    <scg:Dictionary x:TypeArguments="x:String, x:Object">
                      <av:Point x:Key="ShapeLocation">460,757</av:Point>
                      <av:Size x:Key="ShapeSize">200,68.8</av:Size>
                      <av:PointCollection x:Key="ConnectorLocation">560,825.8 560,881.4 430,881.4</av:PointCollection>
                    </scg:Dictionary>
                  </sap:WorkflowViewStateService.ViewState>
                  <Sequence DisplayName="FailedCheck" sap:VirtualizedContainerService.HintSize="200,68.8" sap2010:WorkflowViewState.IdRef="Sequence_8">
                    <sap:WorkflowViewStateService.ViewState>
                      <scg:Dictionary x:TypeArguments="x:String, x:Object">
                        <x:Boolean x:Key="IsExpanded">True</x:Boolean>
                      </scg:Dictionary>
                    </sap:WorkflowViewStateService.ViewState>
                    <WriteLine DisplayName="Write Line" sap:VirtualizedContainerService.HintSize="262,61" sap2010:WorkflowViewState.IdRef="WriteLine_5" Text="No retries left" />
                    <Assign sap:VirtualizedContainerService.HintSize="262,60" sap2010:WorkflowViewState.IdRef="Assign_6">
                      <Assign.To>
                        <OutArgument x:TypeArguments="x:Boolean">
                          <mca:CSharpReference x:TypeArguments="x:Boolean" sap2010:WorkflowViewState.IdRef="CSharpReference`1_9">out_pin_check_successful</mca:CSharpReference>
                        </OutArgument>
                      </Assign.To>
                      <Assign.Value>
                        <InArgument x:TypeArguments="x:Boolean">False</InArgument>
                      </Assign.Value>
                    </Assign>
                  </Sequence>
                  <FlowStep.Next>
                    <FlowStep x:Name="__ReferenceID0">
                      <sap:WorkflowViewStateService.ViewState>
                        <scg:Dictionary x:TypeArguments="x:String, x:Object">
                          <av:Point x:Key="ShapeLocation">230,847</av:Point>
                          <av:Size x:Key="ShapeSize">200,68.8</av:Size>
                        </scg:Dictionary>
                      </sap:WorkflowViewStateService.ViewState>
                      <Sequence DisplayName="FinishedCheck" sap:VirtualizedContainerService.HintSize="200,68.8" sap2010:WorkflowViewState.IdRef="Sequence_6">
                        <sap:WorkflowViewStateService.ViewState>
                          <scg:Dictionary x:TypeArguments="x:String, x:Object">
                            <x:Boolean x:Key="IsExpanded">True</x:Boolean>
                          </scg:Dictionary>
                        </sap:WorkflowViewStateService.ViewState>
                        <WriteLine DisplayName="Write Line" sap:VirtualizedContainerService.HintSize="230,61" sap2010:WorkflowViewState.IdRef="WriteLine_3">
                          <InArgument x:TypeArguments="x:String">
                            <mca:CSharpValue x:TypeArguments="x:String" sap2010:WorkflowViewState.IdRef="CSharpValue`1_10">"Finished pin check. Result is " + out_pin_check_successful.ToString()</mca:CSharpValue>
                          </InArgument>
                        </WriteLine>
                      </Sequence>
                    </FlowStep>
                  </FlowStep.Next>
                </FlowStep>
                <FlowDecision x:Name="__ReferenceID1" DisplayName="CheckRetryTest" sap:VirtualizedContainerService.HintSize="86.4,87.2" sap2010:WorkflowViewState.IdRef="FlowDecision_1">
                  <FlowDecision.Condition>
                    <mca:CSharpValue x:TypeArguments="x:Boolean" sap2010:WorkflowViewState.IdRef="CSharpValue`1_9">local_number_retries &lt; 3</mca:CSharpValue>
                  </FlowDecision.Condition>
                  <sap:WorkflowViewStateService.ViewState>
                    <scg:Dictionary x:TypeArguments="x:String, x:Object">
                      <av:Point x:Key="ShapeLocation">297,696.5</av:Point>
                      <av:Size x:Key="ShapeSize">86.4,87.2</av:Size>
                      <av:PointCollection x:Key="TrueConnector">297,740.1 267,740.1 267,666.5 470,666.5 470,306.5 60,306.5 60,361.4 90,361.4</av:PointCollection>
                      <av:PointCollection x:Key="FalseConnector">383,740 560,740 560,757</av:PointCollection>
                    </scg:Dictionary>
                  </sap:WorkflowViewStateService.ViewState>
                  <FlowDecision.True>
                    <FlowStep x:Name="__ReferenceID6">
                      <sap:WorkflowViewStateService.ViewState>
                        <scg:Dictionary x:TypeArguments="x:String, x:Object">
                          <av:Point x:Key="ShapeLocation">90,327</av:Point>
                          <av:Size x:Key="ShapeSize">200,68.8</av:Size>
                          <av:PointCollection x:Key="ConnectorLocation">190,395.8 190,426.5</av:PointCollection>
                        </scg:Dictionary>
                      </sap:WorkflowViewStateService.ViewState>
                      <Sequence sap2010:Annotation.AnnotationText="Normally this node should perform an interactive call to the Fuzzer and get a pin and compare it to an expected one, but currently, the caller dictates wether the check is correct or no" DisplayName="CheckPin" sap:VirtualizedContainerService.HintSize="200,68.8" sap2010:WorkflowViewState.IdRef="Sequence_4">
                        <sap:WorkflowViewStateService.ViewState>
                          <scg:Dictionary x:TypeArguments="x:String, x:Object">
                            <x:Boolean x:Key="IsExpanded">True</x:Boolean>
                            <x:Boolean x:Key="IsPinned">False</x:Boolean>
                            <x:Boolean x:Key="IsAnnotationDocked">False</x:Boolean>
                          </scg:Dictionary>
                        </sap:WorkflowViewStateService.ViewState>
                        <WriteLine DisplayName="Write Line" sap:VirtualizedContainerService.HintSize="569,61" sap2010:WorkflowViewState.IdRef="WriteLine_1">
                          <InArgument x:TypeArguments="x:String">
                            <mca:CSharpValue x:TypeArguments="x:String" sap2010:WorkflowViewState.IdRef="CSharpValue`1_4">"Pin check. Retry number: " + local_number_retries.ToString()</mca:CSharpValue>
                          </InArgument>
                        </WriteLine>
                        <If sap2010:Annotation.AnnotationText="@Expression&#xA;{{& quot;expression & quot;:&quot;actual_pin_values.GetElementAt(local_number_retries) == expected_pin&quot;}}" sap:VirtualizedContainerService.HintSize="569,260" sap2010:WorkflowViewState.IdRef="If_1">
                          <If.Condition>
                            <InArgument x:TypeArguments="x:Boolean">
                              <mca:CSharpValue x:TypeArguments="x:Boolean" sap2010:WorkflowViewState.IdRef="CSharpValue`1_5">actual_pin_values.ElementAt(local_number_retries) == expected_pin</mca:CSharpValue>
                            </InArgument>
                          </If.Condition>
                          <sap:WorkflowViewStateService.ViewState>
                            <scg:Dictionary x:TypeArguments="x:String, x:Object">
                              <x:Boolean x:Key="IsAnnotationDocked">True</x:Boolean>
                            </scg:Dictionary>
                          </sap:WorkflowViewStateService.ViewState>
                          <If.Then>
                            <Assign sap:VirtualizedContainerService.HintSize="262,60" sap2010:WorkflowViewState.IdRef="Assign_2">
                              <Assign.To>
                                <OutArgument x:TypeArguments="x:Boolean">
                                  <mca:CSharpReference x:TypeArguments="x:Boolean" sap2010:WorkflowViewState.IdRef="CSharpReference`1_5">local_pin_test</mca:CSharpReference>
                                </OutArgument>
                              </Assign.To>
                              <Assign.Value>
                                <InArgument x:TypeArguments="x:Boolean">True</InArgument>
                              </Assign.Value>
                            </Assign>
                          </If.Then>
                          <If.Else>
                            <Assign sap:VirtualizedContainerService.HintSize="262,60" sap2010:WorkflowViewState.IdRef="Assign_3">
                              <Assign.To>
                                <OutArgument x:TypeArguments="x:Boolean">
                                  <mca:CSharpReference x:TypeArguments="x:Boolean" sap2010:WorkflowViewState.IdRef="CSharpReference`1_6">local_pin_test</mca:CSharpReference>
                                </OutArgument>
                              </Assign.To>
                              <Assign.Value>
                                <InArgument x:TypeArguments="x:Boolean">False</InArgument>
                              </Assign.Value>
                            </Assign>
                          </If.Else>
                        </If>
                      </Sequence>
                      <FlowStep.Next>
                        <FlowDecision x:Name="__ReferenceID5" DisplayName="pinTest0" sap:VirtualizedContainerService.HintSize="70,87.2" sap2010:WorkflowViewState.IdRef="FlowDecision_2">
                          <FlowDecision.Condition>
                            <mca:CSharpValue x:TypeArguments="x:Boolean" sap2010:WorkflowViewState.IdRef="CSharpValue`1_6">local_pin_test == true</mca:CSharpValue>
                          </FlowDecision.Condition>
                          <sap:WorkflowViewStateService.ViewState>
                            <scg:Dictionary x:TypeArguments="x:String, x:Object">
                              <av:Point x:Key="ShapeLocation">155,426.5</av:Point>
                              <av:Size x:Key="ShapeSize">70,87.2</av:Size>
                              <av:PointCollection x:Key="FalseConnector">225,470 340,470 340,567</av:PointCollection>
                              <av:PointCollection x:Key="TrueConnector">155,470 120,470 120,636</av:PointCollection>
                            </scg:Dictionary>
                          </sap:WorkflowViewStateService.ViewState>
                          <FlowDecision.True>
                            <FlowStep x:Name="__ReferenceID4">
                              <sap:WorkflowViewStateService.ViewState>
                                <scg:Dictionary x:TypeArguments="x:String, x:Object">
                                  <av:Point x:Key="ShapeLocation">20,636</av:Point>
                                  <av:Size x:Key="ShapeSize">200,68.8</av:Size>
                                  <av:PointCollection x:Key="ConnectorLocation">120,704.8 120,881.4 230,881.4</av:PointCollection>
                                </scg:Dictionary>
                              </sap:WorkflowViewStateService.ViewState>
                              <Sequence DisplayName="SucceedCheck" sap:VirtualizedContainerService.HintSize="200,68.8" sap2010:WorkflowViewState.IdRef="Sequence_5">
                                <sap:WorkflowViewStateService.ViewState>
                                  <scg:Dictionary x:TypeArguments="x:String, x:Object">
                                    <x:Boolean x:Key="IsExpanded">True</x:Boolean>
                                  </scg:Dictionary>
                                </sap:WorkflowViewStateService.ViewState>
                                <WriteLine DisplayName="Write Line" sap:VirtualizedContainerService.HintSize="262.4,62.4" sap2010:WorkflowViewState.IdRef="WriteLine_2" Text="Correct pin" />
                                <Assign sap:VirtualizedContainerService.HintSize="262.4,59.6" sap2010:WorkflowViewState.IdRef="Assign_4">
                                  <Assign.To>
                                    <OutArgument x:TypeArguments="x:Boolean">
                                      <mca:CSharpReference x:TypeArguments="x:Boolean" sap2010:WorkflowViewState.IdRef="CSharpReference`1_7">out_pin_check_successful</mca:CSharpReference>
                                    </OutArgument>
                                  </Assign.To>
                                  <Assign.Value>
                                    <InArgument x:TypeArguments="x:Boolean">True</InArgument>
                                  </Assign.Value>
                                </Assign>
                              </Sequence>
                              <FlowStep.Next>
                                <x:Reference>__ReferenceID0</x:Reference>
                              </FlowStep.Next>
                            </FlowStep>
                          </FlowDecision.True>
                          <FlowDecision.False>
                            <FlowStep x:Name="__ReferenceID3">
                              <sap:WorkflowViewStateService.ViewState>
                                <scg:Dictionary x:TypeArguments="x:String, x:Object">
                                  <av:Point x:Key="ShapeLocation">240,567</av:Point>
                                  <av:Size x:Key="ShapeSize">200,68.8</av:Size>
                                  <av:PointCollection x:Key="ConnectorLocation">340,635.8 340,696.5</av:PointCollection>
                                </scg:Dictionary>
                              </sap:WorkflowViewStateService.ViewState>
                              <Sequence DisplayName="RetryCheck" sap:VirtualizedContainerService.HintSize="200,68.8" sap2010:WorkflowViewState.IdRef="Sequence_7">
                                <sap:WorkflowViewStateService.ViewState>
                                  <scg:Dictionary x:TypeArguments="x:String, x:Object">
                                    <x:Boolean x:Key="IsExpanded">True</x:Boolean>
                                  </scg:Dictionary>
                                </sap:WorkflowViewStateService.ViewState>
                                <WriteLine DisplayName="Write Line" sap:VirtualizedContainerService.HintSize="262,61" sap2010:WorkflowViewState.IdRef="WriteLine_4">
                                  <InArgument x:TypeArguments="x:String">
                                    <mca:CSharpValue x:TypeArguments="x:String" sap2010:WorkflowViewState.IdRef="CSharpValue`1_7">"Wrong pin. Expected value: " + expected_pin.ToString() + ". Actual value: " + actual_pin_values.ElementAt(local_number_retries).ToString() + ". Are there any retries left?"</mca:CSharpValue>
                                  </InArgument>
                                </WriteLine>
                                <Assign sap:VirtualizedContainerService.HintSize="262,60" sap2010:WorkflowViewState.IdRef="Assign_5">
                                  <Assign.To>
                                    <OutArgument x:TypeArguments="x:Int32">
                                      <mca:CSharpReference x:TypeArguments="x:Int32" sap2010:WorkflowViewState.IdRef="CSharpReference`1_8">local_number_retries</mca:CSharpReference>
                                    </OutArgument>
                                  </Assign.To>
                                  <Assign.Value>
                                    <InArgument x:TypeArguments="x:Int32">
                                      <mca:CSharpValue x:TypeArguments="x:Int32" sap2010:WorkflowViewState.IdRef="CSharpValue`1_8">local_number_retries + 1</mca:CSharpValue>
                                    </InArgument>
                                  </Assign.Value>
                                </Assign>
                              </Sequence>
                              <FlowStep.Next>
                                <x:Reference>__ReferenceID1</x:Reference>
                              </FlowStep.Next>
                            </FlowStep>
                          </FlowDecision.False>
                        </FlowDecision>
                      </FlowStep.Next>
                    </FlowStep>
                  </FlowDecision.True>
                  <FlowDecision.False>
                    <x:Reference>__ReferenceID2</x:Reference>
                  </FlowDecision.False>
                </FlowDecision>
                <x:Reference>__ReferenceID3</x:Reference>
                <x:Reference>__ReferenceID4</x:Reference>
                <x:Reference>__ReferenceID5</x:Reference>
                <x:Reference>__ReferenceID6</x:Reference>
                <x:Reference>__ReferenceID0</x:Reference>
                <FlowStep x:Name="__ReferenceID8">
                  <sap:WorkflowViewStateService.ViewState>
                    <scg:Dictionary x:TypeArguments="x:String, x:Object">
                      <av:Point x:Key="ShapeLocation">90,87</av:Point>
                      <av:Size x:Key="ShapeSize">200,68.8</av:Size>
                      <av:PointCollection x:Key="ConnectorLocation">190,155.8 190,187</av:PointCollection>
                    </scg:Dictionary>
                  </sap:WorkflowViewStateService.ViewState>
                  <Sequence DisplayName="Get expected pin value" sap:VirtualizedContainerService.HintSize="200,68.8" sap2010:WorkflowViewState.IdRef="Sequence_2">
                    <Sequence.Variables>
                      <Variable x:TypeArguments="sd:DataTable" Name="local_test_data_expected" />
                    </Sequence.Variables>
                    <sap:WorkflowViewStateService.ViewState>
                      <scg:Dictionary x:TypeArguments="x:String, x:Object">
                        <x:Boolean x:Key="IsExpanded">True</x:Boolean>
                      </scg:Dictionary>
                    </sap:WorkflowViewStateService.ViewState>
                    <ui:ReadCsvFile Encoding="{{x:Null}}" Delimitator="Comma" DisplayName="Read CSV" FilePath="pin_mocked_data.csv" sap:VirtualizedContainerService.HintSize="334,152" sap2010:WorkflowViewState.IdRef="ReadCsvFile_1">
                      <ui:ReadCsvFile.DataTable>
                        <OutArgument x:TypeArguments="sd:DataTable">
                          <mca:CSharpReference x:TypeArguments="sd:DataTable" sap2010:WorkflowViewState.IdRef="CSharpReference`1_1">local_test_data_expected</mca:CSharpReference>
                        </OutArgument>
                      </ui:ReadCsvFile.DataTable>
                    </ui:ReadCsvFile>
                    <Assign DisplayName="Set expected pin" sap:VirtualizedContainerService.HintSize="334,60" sap2010:WorkflowViewState.IdRef="Assign_1">
                      <Assign.To>
                        <OutArgument x:TypeArguments="x:Int32">
                          <mca:CSharpReference x:TypeArguments="x:Int32" sap2010:WorkflowViewState.IdRef="CSharpReference`1_2">expected_pin</mca:CSharpReference>
                        </OutArgument>
                      </Assign.To>
                      <Assign.Value>
                        <InArgument x:TypeArguments="x:Int32">
                          <mca:CSharpValue x:TypeArguments="x:Int32" sap2010:WorkflowViewState.IdRef="CSharpValue`1_2">Int32.Parse(local_test_data_expected.Rows[0]["Pin:expected_pin"].ToString())</mca:CSharpValue>
                        </InArgument>
                      </Assign.Value>
                    </Assign>
                  </Sequence>
                  <FlowStep.Next>
                    <FlowStep x:Name="__ReferenceID7">
                      <sap:WorkflowViewStateService.ViewState>
                        <scg:Dictionary x:TypeArguments="x:String, x:Object">
                          <av:Point x:Key="ShapeLocation">90,187</av:Point>
                          <av:Size x:Key="ShapeSize">200,68.8</av:Size>
                          <av:PointCollection x:Key="ConnectorLocation">190,255.8 190,327</av:PointCollection>
                        </scg:Dictionary>
                      </sap:WorkflowViewStateService.ViewState>
                      <Sequence DisplayName="Get actual pin values" sap:VirtualizedContainerService.HintSize="200,68.8" sap2010:WorkflowViewState.IdRef="Sequence_3">
                        <Sequence.Variables>
                          <Variable x:TypeArguments="sd:DataTable" Name="local_test_data_actual" />
                        </Sequence.Variables>
                        <sap:WorkflowViewStateService.ViewState>
                          <scg:Dictionary x:TypeArguments="x:String, x:Object">
                            <x:Boolean x:Key="IsExpanded">True</x:Boolean>
                          </scg:Dictionary>
                        </sap:WorkflowViewStateService.ViewState>
                        <ui:ReadCsvFile Encoding="{{x:Null}}" sap2010:Annotation.AnnotationText="@This is an anotation&#xA;Actually a text label" Delimitator="Comma" DisplayName="Read CSV" FilePath="pin_real_data.csv" sap:VirtualizedContainerService.HintSize="334,194" sap2010:WorkflowViewState.IdRef="ReadCsvFile_2">
                          <ui:ReadCsvFile.DataTable>
                            <OutArgument x:TypeArguments="sd:DataTable">
                              <mca:CSharpReference x:TypeArguments="sd:DataTable" sap2010:WorkflowViewState.IdRef="CSharpReference`1_3">local_test_data_actual</mca:CSharpReference>
                            </OutArgument>
                          </ui:ReadCsvFile.DataTable>
                          <sap:WorkflowViewStateService.ViewState>
                            <scg:Dictionary x:TypeArguments="x:String, x:Object">
                              <x:Boolean x:Key="IsAnnotationDocked">True</x:Boolean>
                            </scg:Dictionary>
                          </sap:WorkflowViewStateService.ViewState>
                        </ui:ReadCsvFile>
                        <ui:InvokeCode ContinueOnError="{{x:Null}}" Code="var tempArr = local_test_data.Rows[0][&quot;Pin:actual_pin_values&quot;].ToString().Split(&quot;;&quot;.ElementAt(0));&#xA;List&lt;Int32&gt; intList = new List&lt;Int32&gt;();&#xA;foreach(var val in tempArr) {{&  # xA;&#x9;intList.Add(Int32.Parse(val));&#xA;}}&#xA;actual_pin_values = intList.ToArray();" DisplayName="Set actual values" sap:VirtualizedContainerService.HintSize="334,164" sap2010:WorkflowViewState.IdRef="InvokeCode_1" Language="CSharp">
            < ui:InvokeCode.Arguments>
                            <InOutArgument x:TypeArguments="s:Int32[]" x:Key="actual_pin_values">
                              <mca:CSharpReference x:TypeArguments="s:Int32[]" sap2010:WorkflowViewState.IdRef="CSharpReference`1_4">actual_pin_values</mca:CSharpReference>
                            </InOutArgument>
                            <InArgument x:TypeArguments="sd:DataTable" x:Key="local_test_data">
                              <mca:CSharpValue x:TypeArguments="sd:DataTable" sap2010:WorkflowViewState.IdRef="CSharpValue`1_3">local_test_data_actual</mca:CSharpValue>
                            </InArgument>
                          </ui:InvokeCode.Arguments>
                        </ui:InvokeCode>
                      </Sequence>
                      <FlowStep.Next>
                        <x:Reference>__ReferenceID6</x:Reference>
                      </FlowStep.Next>
                    </FlowStep>
                  </FlowStep.Next>
                </FlowStep>
                <x:Reference>__ReferenceID7</x:Reference>
              </Flowchart>
            </Activity>
            """
        file_content = file_content.replace('\n', '')

        # Remove extra spaces
        file_content = ' '.join(file_content.split())
        return file_content

    def generate_flowchart_main(self, loan_type, term_type, obtained_result, pin_check_successful, loan, term):
        file_content =  f"""
        <Activity mc:Ignorable="sap sap2010" x:Class="Main" xmlns="http://schemas.microsoft.com/netfx/2009/xaml/activities" xmlns:av="http://schemas.microsoft.com/winfx/2006/xaml/presentation" xmlns:mc="http://schemas.openxmlformats.org/markup-compatibility/2006" xmlns:mca="clr-namespace:Microsoft.CSharp.Activities;assembly=System.Activities" xmlns:sap="http://schemas.microsoft.com/netfx/2009/xaml/activities/presentation" xmlns:sap2010="http://schemas.microsoft.com/netfx/2010/xaml/activities/presentation" xmlns:scg="clr-namespace:System.Collections.Generic;assembly=mscorlib" xmlns:sco="clr-namespace:System.Collections.ObjectModel;assembly=mscorlib" xmlns:ui="http://schemas.uipath.com/workflow/activities" xmlns:x="http://schemas.microsoft.com/winfx/2006/xaml">
  <x:Members>
    <x:Property Name="loan" Type="InArgument(x:Int32)" />
    <x:Property Name="term" Type="InArgument(x:Int32)" />
  </x:Members>
  <sap2010:ExpressionActivityEditor.ExpressionActivityEditor>C#</sap2010:ExpressionActivityEditor.ExpressionActivityEditor>
  <sap:VirtualizedContainerService.HintSize>2434.8,1682</sap:VirtualizedContainerService.HintSize>
  <sap2010:WorkflowViewState.IdRef>ActivityBuilder_1</sap2010:WorkflowViewState.IdRef>
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
      <x:String>System.Text</x:String>
      <x:String>System.Xml.Linq</x:String>
      <x:String>UiPath.Core</x:String>
      <x:String>UiPath.Core.Activities</x:String>
      <x:String>System.Windows.Markup</x:String>
      <x:String>System.Collections.ObjectModel</x:String>
      <x:String>System.Runtime.Serialization</x:String>
      <x:String>System.Activities.DynamicUpdate</x:String>
      <x:String>System.Linq.Expressions</x:String>
    </sco:Collection>
  </TextExpression.NamespacesForImplementation>
  <TextExpression.ReferencesForImplementation>
    <sco:Collection x:TypeArguments="AssemblyReference">
      <AssemblyReference>Microsoft.CSharp</AssemblyReference>
      <AssemblyReference>System</AssemblyReference>
      <AssemblyReference>System.Core</AssemblyReference>
      <AssemblyReference>System.Activities</AssemblyReference>
      <AssemblyReference>System.Data</AssemblyReference>
      <AssemblyReference>System.Runtime.Serialization</AssemblyReference>
      <AssemblyReference>System.ServiceModel</AssemblyReference>
      <AssemblyReference>System.ServiceModel.Activities</AssemblyReference>
      <AssemblyReference>System.Xaml</AssemblyReference>
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
      <AssemblyReference>System.Data.DataSetExtensions</AssemblyReference>
      <AssemblyReference>Microsoft.Bcl.AsyncInterfaces</AssemblyReference>
      <AssemblyReference>System.ValueTuple</AssemblyReference>
      <AssemblyReference>System.ComponentModel.Composition</AssemblyReference>
      <AssemblyReference>UiPath.Mail</AssemblyReference>
      <AssemblyReference>UiPath.Excel</AssemblyReference>
      <AssemblyReference>System.Memory</AssemblyReference>
      <AssemblyReference>UiPath.OCR.Activities.Design</AssemblyReference>
      <AssemblyReference>UiPath.UIAutomationCore</AssemblyReference>
      <AssemblyReference>UiPath.System.Activities.Design</AssemblyReference>
    </sco:Collection>
  </TextExpression.ReferencesForImplementation>
  <Flowchart sap2010:Annotation.AnnotationText="@Variables&#xA;{{&quot;obtained_result&quot;:{{&quot;pattern&quot;:&quot;[A-Z][a-Z]*&quot;}}, &quot;loan&quot;:{{&quot;userInput&quot;:&quot;True&quot;,&quot;min&quot;:0,&quot;max&quot;:1000000000}}, &quot;term&quot;:{{&quot;userInput&quot;: &quot;True&quot;,&quot;min&quot;:1,&quot;max&quot;:35}}" DisplayName="Main" sap:VirtualizedContainerService.HintSize="2444.8,1516.8" sap2010:WorkflowViewState.IdRef="Flowchart_1">
    <Flowchart.Variables>
      <Variable x:TypeArguments="x:String" Name="loan_type" />
      <Variable x:TypeArguments="x:String" Name="term_type" />
      <Variable x:TypeArguments="x:String" Name="obtained_result" />
      <Variable x:TypeArguments="x:Boolean" Name="pin_check_successful" />
    </Flowchart.Variables>
    <sap:WorkflowViewStateService.ViewState>
      <scg:Dictionary x:TypeArguments="x:String, x:Object">
        <x:Boolean x:Key="IsExpanded">True</x:Boolean>
        <av:Point x:Key="ShapeLocation">270,2.5</av:Point>
        <av:Size x:Key="ShapeSize">60,75.2</av:Size>
        <av:PointCollection x:Key="ConnectorLocation">300,77.5 300,107.5 276.1,107.5 276.1,126.4</av:PointCollection>
        <x:Double x:Key="Width">2410.682172121039</x:Double>
        <x:Double x:Key="Height">1435.8722474448859</x:Double>
        <x:Boolean x:Key="IsAnnotationDocked">True</x:Boolean>
      </scg:Dictionary>
    </sap:WorkflowViewStateService.ViewState>
    <Flowchart.StartNode>
      <x:Reference>__ReferenceID11</x:Reference>
    </Flowchart.StartNode>
    <FlowDecision x:Name="__ReferenceID11" DisplayName="Node_loanTest0" sap:VirtualizedContainerService.HintSize="90.4,87.2" sap2010:WorkflowViewState.IdRef="FlowDecision_4">
      <FlowDecision.Condition>
        <mca:CSharpValue x:TypeArguments="x:Boolean" sap2010:WorkflowViewState.IdRef="CSharpValue`1_1">loan &lt; 1000</mca:CSharpValue>
      </FlowDecision.Condition>
      <sap:WorkflowViewStateService.ViewState>
        <scg:Dictionary x:TypeArguments="x:String, x:Object">
          <x:Boolean x:Key="IsExpanded">True</x:Boolean>
          <av:Point x:Key="ShapeLocation">231.6,126.4</av:Point>
          <av:Size x:Key="ShapeSize">90.4,87.2</av:Size>
          <av:PointCollection x:Key="TrueConnector">231.6,170 190,170 190,256</av:PointCollection>
          <av:PointCollection x:Key="FalseConnector">322,170 352,170 352,137.333333333333 504.2,137.333333333333 504.2,167.333333333333</av:PointCollection>
        </scg:Dictionary>
      </sap:WorkflowViewStateService.ViewState>
      <FlowDecision.True>
        <FlowStep x:Name="__ReferenceID2">
          <sap:WorkflowViewStateService.ViewState>
            <scg:Dictionary x:TypeArguments="x:String, x:Object">
              <av:Point x:Key="ShapeLocation">90,256</av:Point>
              <av:Size x:Key="ShapeSize">200,68.8</av:Size>
              <av:PointCollection x:Key="ConnectorLocation">190,324.8 190,446.4 369.1,446.4 369.1,476.4</av:PointCollection>
            </scg:Dictionary>
          </sap:WorkflowViewStateService.ViewState>
          <Sequence DisplayName="LowVolumeLoan" sap:VirtualizedContainerService.HintSize="200,68.8" sap2010:WorkflowViewState.IdRef="Sequence_1">
            <sap:WorkflowViewStateService.ViewState>
              <scg:Dictionary x:TypeArguments="x:String, x:Object">
                <x:Boolean x:Key="IsExpanded">True</x:Boolean>
              </scg:Dictionary>
            </sap:WorkflowViewStateService.ViewState>
            <WriteLine DisplayName="Write Line" sap:VirtualizedContainerService.HintSize="262,61" sap2010:WorkflowViewState.IdRef="WriteLine_1" Text="Low - Volume loan" />
            <Assign sap:VirtualizedContainerService.HintSize="262,60" sap2010:WorkflowViewState.IdRef="Assign_1">
              <Assign.To>
                <OutArgument x:TypeArguments="x:String">
                  <mca:CSharpReference x:TypeArguments="x:String" sap2010:WorkflowViewState.IdRef="CSharpReference`1_1">loan_type</mca:CSharpReference>
                </OutArgument>
              </Assign.To>
              <Assign.Value>
                <InArgument x:TypeArguments="x:String">Low-Volume Loan</InArgument>
              </Assign.Value>
            </Assign>
          </Sequence>
          <FlowStep.Next>
            <FlowDecision x:Name="__ReferenceID1" DisplayName=" Term_test0 " sap:VirtualizedContainerService.HintSize="70,87.2" sap2010:WorkflowViewState.IdRef="FlowDecision_1">
              <FlowDecision.Condition>
                <mca:CSharpValue x:TypeArguments="x:Boolean" sap2010:WorkflowViewState.IdRef="CSharpValue`1_4">term &lt; 5</mca:CSharpValue>
              </FlowDecision.Condition>
              <sap:WorkflowViewStateService.ViewState>
                <scg:Dictionary x:TypeArguments="x:String, x:Object">
                  <x:Boolean x:Key="IsExpanded">True</x:Boolean>
                  <av:Point x:Key="ShapeLocation">351.6,476.4</av:Point>
                  <av:Size x:Key="ShapeSize">70,87.2</av:Size>
                  <av:PointCollection x:Key="TrueConnector">351.6,520 260,520 260,566</av:PointCollection>
                  <av:PointCollection x:Key="FalseConnector">421.6,519.733333333333 560,519.733333333333 560,566</av:PointCollection>
                </scg:Dictionary>
              </sap:WorkflowViewStateService.ViewState>
              <FlowDecision.True>
                <FlowStep x:Name="__ReferenceID6">
                  <sap:WorkflowViewStateService.ViewState>
                    <scg:Dictionary x:TypeArguments="x:String, x:Object">
                      <av:Point x:Key="ShapeLocation">160,566</av:Point>
                      <av:Size x:Key="ShapeSize">200,68.8</av:Size>
                      <av:PointCollection x:Key="ConnectorLocation">260,635.333333333333 260,690.666666666667 310,690.666666666667</av:PointCollection>
                    </scg:Dictionary>
                  </sap:WorkflowViewStateService.ViewState>
                  <Sequence DisplayName="Short - Term" sap:VirtualizedContainerService.HintSize="200,68.8" sap2010:WorkflowViewState.IdRef="Sequence_2">
                    <sap:WorkflowViewStateService.ViewState>
                      <scg:Dictionary x:TypeArguments="x:String, x:Object">
                        <x:Boolean x:Key="IsExpanded">True</x:Boolean>
                      </scg:Dictionary>
                    </sap:WorkflowViewStateService.ViewState>
                    <WriteLine DisplayName="Write Line" sap:VirtualizedContainerService.HintSize="262,61" sap2010:WorkflowViewState.IdRef="WriteLine_2" Text="Short - Term" />
                    <Assign sap:VirtualizedContainerService.HintSize="262,60" sap2010:WorkflowViewState.IdRef="Assign_2">
                      <Assign.To>
                        <OutArgument x:TypeArguments="x:String">
                          <mca:CSharpReference x:TypeArguments="x:String" sap2010:WorkflowViewState.IdRef="CSharpReference`1_6">term_type</mca:CSharpReference>
                        </OutArgument>
                      </Assign.To>
                      <Assign.Value>
                        <InArgument x:TypeArguments="x:String">Short-Term</InArgument>
                      </Assign.Value>
                    </Assign>
                  </Sequence>
                  <FlowStep.Next>
                    <FlowStep x:Name="__ReferenceID0">
                      <sap:WorkflowViewStateService.ViewState>
                        <scg:Dictionary x:TypeArguments="x:String, x:Object">
                          <av:Point x:Key="ShapeLocation">310,656</av:Point>
                          <av:Size x:Key="ShapeSize">200,68.8</av:Size>
                        </scg:Dictionary>
                      </sap:WorkflowViewStateService.ViewState>
                      <Sequence DisplayName="Output rate " sap:VirtualizedContainerService.HintSize="200,68.8" sap2010:WorkflowViewState.IdRef="Sequence_3">
                        <sap:WorkflowViewStateService.ViewState>
                          <scg:Dictionary x:TypeArguments="x:String, x:Object">
                            <x:Boolean x:Key="IsExpanded">True</x:Boolean>
                          </scg:Dictionary>
                        </sap:WorkflowViewStateService.ViewState>
                        <WriteLine DisplayName="Write Line" sap:VirtualizedContainerService.HintSize="262,61" sap2010:WorkflowViewState.IdRef="WriteLine_3">
                          <InArgument x:TypeArguments="x:String">
                            <mca:CSharpValue x:TypeArguments="x:String" sap2010:WorkflowViewState.IdRef="CSharpValue`1_5" xml:space="preserve">"The output rate is: " + loan_type+ " and  " + term_type</mca:CSharpValue>
                          </InArgument>
                        </WriteLine>
                        <Assign sap:VirtualizedContainerService.HintSize="262,60" sap2010:WorkflowViewState.IdRef="Assign_3">
                          <Assign.To>
                            <OutArgument x:TypeArguments="x:String">
                              <mca:CSharpReference x:TypeArguments="x:String" sap2010:WorkflowViewState.IdRef="CSharpReference`1_7">obtained_result</mca:CSharpReference>
                            </OutArgument>
                          </Assign.To>
                          <Assign.Value>
                            <InArgument x:TypeArguments="x:String">
                              <mca:CSharpValue x:TypeArguments="x:String" sap2010:WorkflowViewState.IdRef="CSharpValue`1_6">loan_type + " " + term_type</mca:CSharpValue>
                            </InArgument>
                          </Assign.Value>
                        </Assign>
                      </Sequence>
                    </FlowStep>
                  </FlowStep.Next>
                </FlowStep>
              </FlowDecision.True>
              <FlowDecision.False>
                <FlowStep x:Name="__ReferenceID7">
                  <sap:WorkflowViewStateService.ViewState>
                    <scg:Dictionary x:TypeArguments="x:String, x:Object">
                      <av:Point x:Key="ShapeLocation">460,566</av:Point>
                      <av:Size x:Key="ShapeSize">200,68.8</av:Size>
                      <av:PointCollection x:Key="ConnectorLocation">560,635.333333333333 560,690.666666666667 510,690.666666666667</av:PointCollection>
                    </scg:Dictionary>
                  </sap:WorkflowViewStateService.ViewState>
                  <Sequence DisplayName="Long term" sap:VirtualizedContainerService.HintSize="200,68.8" sap2010:WorkflowViewState.IdRef="Sequence_4">
                    <sap:WorkflowViewStateService.ViewState>
                      <scg:Dictionary x:TypeArguments="x:String, x:Object">
                        <x:Boolean x:Key="IsExpanded">True</x:Boolean>
                      </scg:Dictionary>
                    </sap:WorkflowViewStateService.ViewState>
                    <WriteLine DisplayName="Write Line" sap:VirtualizedContainerService.HintSize="262,61" sap2010:WorkflowViewState.IdRef="WriteLine_4" Text="Long - Term" />
                    <Assign sap:VirtualizedContainerService.HintSize="262,60" sap2010:WorkflowViewState.IdRef="Assign_4">
                      <Assign.To>
                        <OutArgument x:TypeArguments="x:String">
                          <mca:CSharpReference x:TypeArguments="x:String" sap2010:WorkflowViewState.IdRef="CSharpReference`1_5">term_type</mca:CSharpReference>
                        </OutArgument>
                      </Assign.To>
                      <Assign.Value>
                        <InArgument x:TypeArguments="x:String">Long-Term</InArgument>
                      </Assign.Value>
                    </Assign>
                  </Sequence>
                  <FlowStep.Next>
                    <x:Reference>__ReferenceID0</x:Reference>
                  </FlowStep.Next>
                </FlowStep>
              </FlowDecision.False>
            </FlowDecision>
          </FlowStep.Next>
        </FlowStep>
      </FlowDecision.True>
      <FlowDecision.False>
        <FlowDecision x:Name="__ReferenceID3" sap2010:Annotation.AnnotationText="@Expression&#xA;{{&quot;expression&quot;:&quot;loan &gt;= 1000 and loan &lt; 100000&quot;}}" DisplayName="Node_loanTest1" sap:VirtualizedContainerService.HintSize="148.4,164.8" sap2010:WorkflowViewState.IdRef="FlowDecision_3">
          <FlowDecision.Condition>
            <mca:CSharpValue x:TypeArguments="x:Boolean" sap2010:WorkflowViewState.IdRef="CSharpValue`1_2">loan &gt;= 1000 &amp;&amp; loan &lt; 100000</mca:CSharpValue>
          </FlowDecision.Condition>
          <sap:WorkflowViewStateService.ViewState>
            <scg:Dictionary x:TypeArguments="x:String, x:Object">
              <x:Boolean x:Key="IsExpanded">True</x:Boolean>
              <av:Point x:Key="ShapeLocation">430,167.333333333333</av:Point>
              <av:Size x:Key="ShapeSize">148.4,164.8</av:Size>
              <av:PointCollection x:Key="TrueConnector">430,249.733333333333 400,249.733333333333 400,346</av:PointCollection>
              <av:PointCollection x:Key="FalseConnector">578.4,249.733333333333 620,249.733333333333 620,346</av:PointCollection>
              <x:Boolean x:Key="IsAnnotationDocked">True</x:Boolean>
            </scg:Dictionary>
          </sap:WorkflowViewStateService.ViewState>
          <FlowDecision.True>
            <FlowStep x:Name="__ReferenceID4">
              <sap:WorkflowViewStateService.ViewState>
                <scg:Dictionary x:TypeArguments="x:String, x:Object">
                  <av:Point x:Key="ShapeLocation">300,346</av:Point>
                  <av:Size x:Key="ShapeSize">200,68.8</av:Size>
                  <av:PointCollection x:Key="ConnectorLocation">400,414.8 400,444.8 386.6,444.8 386.6,476.4</av:PointCollection>
                </scg:Dictionary>
              </sap:WorkflowViewStateService.ViewState>
              <Sequence DisplayName="MidVolumeLoan" sap:VirtualizedContainerService.HintSize="200,68.8" sap2010:WorkflowViewState.IdRef="Sequence_5">
                <sap:WorkflowViewStateService.ViewState>
                  <scg:Dictionary x:TypeArguments="x:String, x:Object">
                    <x:Boolean x:Key="IsExpanded">True</x:Boolean>
                  </scg:Dictionary>
                </sap:WorkflowViewStateService.ViewState>
                <WriteLine DisplayName="Write Line" sap:VirtualizedContainerService.HintSize="262,61" sap2010:WorkflowViewState.IdRef="WriteLine_5" Text="Mid - Volume loan" />
                <Assign sap:VirtualizedContainerService.HintSize="262,60" sap2010:WorkflowViewState.IdRef="Assign_5">
                  <Assign.To>
                    <OutArgument x:TypeArguments="x:String">
                      <mca:CSharpReference x:TypeArguments="x:String" sap2010:WorkflowViewState.IdRef="CSharpReference`1_2">loan_type</mca:CSharpReference>
                    </OutArgument>
                  </Assign.To>
                  <Assign.Value>
                    <InArgument x:TypeArguments="x:String">Mid-Volume Loan</InArgument>
                  </Assign.Value>
                </Assign>
              </Sequence>
              <FlowStep.Next>
                <x:Reference>__ReferenceID1</x:Reference>
              </FlowStep.Next>
            </FlowStep>
          </FlowDecision.True>
          <FlowDecision.False>
            <FlowStep x:Name="__ReferenceID5">
              <sap:WorkflowViewStateService.ViewState>
                <scg:Dictionary x:TypeArguments="x:String, x:Object">
                  <av:Point x:Key="ShapeLocation">520,346</av:Point>
                  <av:Size x:Key="ShapeSize">200,68.8</av:Size>
                  <av:PointCollection x:Key="ConnectorLocation">720,380.4 870,380.4 870,403.6</av:PointCollection>
                </scg:Dictionary>
              </sap:WorkflowViewStateService.ViewState>
              <Sequence DisplayName="HighVolumeLoan" sap:VirtualizedContainerService.HintSize="200,68.8" sap2010:WorkflowViewState.IdRef="Sequence_6">
                <sap:WorkflowViewStateService.ViewState>
                  <scg:Dictionary x:TypeArguments="x:String, x:Object">
                    <x:Boolean x:Key="IsExpanded">True</x:Boolean>
                  </scg:Dictionary>
                </sap:WorkflowViewStateService.ViewState>
                <WriteLine DisplayName="Write Line" sap:VirtualizedContainerService.HintSize="262,61" sap2010:WorkflowViewState.IdRef="WriteLine_6" Text="High - Volume loan" />
                <Assign sap:VirtualizedContainerService.HintSize="262,60" sap2010:WorkflowViewState.IdRef="Assign_6">
                  <Assign.To>
                    <OutArgument x:TypeArguments="x:String">
                      <mca:CSharpReference x:TypeArguments="x:String" sap2010:WorkflowViewState.IdRef="CSharpReference`1_3">loan_type</mca:CSharpReference>
                    </OutArgument>
                  </Assign.To>
                  <Assign.Value>
                    <InArgument x:TypeArguments="x:String">High-Volume Loan</InArgument>
                  </Assign.Value>
                </Assign>
              </Sequence>
              <FlowStep.Next>
                <FlowStep x:Name="__ReferenceID10">
                  <sap:WorkflowViewStateService.ViewState>
                    <scg:Dictionary x:TypeArguments="x:String, x:Object">
                      <av:Point x:Key="ShapeLocation">770,403.6</av:Point>
                      <av:Size x:Key="ShapeSize">200,52.4</av:Size>
                      <av:PointCollection x:Key="ConnectorLocation">770,429.933333333333 677.5,429.933333333333 677.5,456.5</av:PointCollection>
                    </scg:Dictionary>
                  </sap:WorkflowViewStateService.ViewState>
                  <ui:InvokeWorkflowFile ArgumentsVariable="{{x:Null}}" ContinueOnError="{{x:Null}}" DisplayName="Invoke Pin Check" sap:VirtualizedContainerService.HintSize="200,52.4" sap2010:WorkflowViewState.IdRef="InvokeWorkflowFile_1" LogEntry="No" LogExit="No" UnSafe="False" WorkflowFileName="Pin.xaml">
                    <ui:InvokeWorkflowFile.Arguments>
                      <OutArgument x:TypeArguments="x:Boolean" x:Key="out_pin_check_successful">
                        <mca:CSharpReference x:TypeArguments="x:Boolean" sap2010:WorkflowViewState.IdRef="CSharpReference`1_4">pin_check_successful</mca:CSharpReference>
                      </OutArgument>
                    </ui:InvokeWorkflowFile.Arguments>
                    <sap:WorkflowViewStateService.ViewState>
                      <scg:Dictionary x:TypeArguments="x:String, x:Object">
                        <x:Boolean x:Key="IsExpanded">True</x:Boolean>
                      </scg:Dictionary>
                    </sap:WorkflowViewStateService.ViewState>
                  </ui:InvokeWorkflowFile>
                  <FlowStep.Next>
                    <FlowDecision x:Name="__ReferenceID9" DisplayName="CheckedPin" sap:VirtualizedContainerService.HintSize="70,87.2" sap2010:WorkflowViewState.IdRef="FlowDecision_2">
                      <FlowDecision.Condition>
                        <mca:CSharpValue x:TypeArguments="x:Boolean" sap2010:WorkflowViewState.IdRef="CSharpValue`1_3">pin_check_successful == true</mca:CSharpValue>
                      </FlowDecision.Condition>
                      <sap:WorkflowViewStateService.ViewState>
                        <scg:Dictionary x:TypeArguments="x:String, x:Object">
                          <x:Boolean x:Key="IsExpanded">True</x:Boolean>
                          <av:Point x:Key="ShapeLocation">642.5,456.5</av:Point>
                          <av:Size x:Key="ShapeSize">70,87.2</av:Size>
                          <av:PointCollection x:Key="TrueConnector">642.5,499.833333333333 612.5,499.833333333333 612.5,446.4 404.1,446.4 404.1,476.4</av:PointCollection>
                          <av:PointCollection x:Key="FalseConnector">712.5,499.833333333333 850,499.833333333333 850,566</av:PointCollection>
                        </scg:Dictionary>
                      </sap:WorkflowViewStateService.ViewState>
                      <FlowDecision.True>
                        <x:Reference>__ReferenceID1</x:Reference>
                      </FlowDecision.True>
                      <FlowDecision.False>
                        <FlowStep x:Name="__ReferenceID8">
                          <sap:WorkflowViewStateService.ViewState>
                            <scg:Dictionary x:TypeArguments="x:String, x:Object">
                              <av:Point x:Key="ShapeLocation">750,566</av:Point>
                              <av:Size x:Key="ShapeSize">200,68.8</av:Size>
                            </scg:Dictionary>
                          </sap:WorkflowViewStateService.ViewState>
                          <Sequence DisplayName="Fail" sap:VirtualizedContainerService.HintSize="200,68.8" sap2010:WorkflowViewState.IdRef="Sequence_7">
                            <sap:WorkflowViewStateService.ViewState>
                              <scg:Dictionary x:TypeArguments="x:String, x:Object">
                                <x:Boolean x:Key="IsExpanded">True</x:Boolean>
                              </scg:Dictionary>
                            </sap:WorkflowViewStateService.ViewState>
                            <WriteLine DisplayName="Write Line" sap:VirtualizedContainerService.HintSize="230,61" sap2010:WorkflowViewState.IdRef="WriteLine_7" Text="Pin check failed. Process ended." />
                          </Sequence>
                        </FlowStep>
                      </FlowDecision.False>
                    </FlowDecision>
                  </FlowStep.Next>
                </FlowStep>
              </FlowStep.Next>
            </FlowStep>
          </FlowDecision.False>
        </FlowDecision>
      </FlowDecision.False>
    </FlowDecision>
    <x:Reference>__ReferenceID2</x:Reference>
    <x:Reference>__ReferenceID3</x:Reference>
    <x:Reference>__ReferenceID4</x:Reference>
    <x:Reference>__ReferenceID5</x:Reference>
    <x:Reference>__ReferenceID1</x:Reference>
    <x:Reference>__ReferenceID6</x:Reference>
    <x:Reference>__ReferenceID7</x:Reference>
    <x:Reference>__ReferenceID0</x:Reference>
    <x:Reference>__ReferenceID8</x:Reference>
    <x:Reference>__ReferenceID9</x:Reference>
    <x:Reference>__ReferenceID10</x:Reference>
  </Flowchart>
</Activity>
"""
        file_content = file_content.replace('\n', '')

        # Remove extra spaces
        file_content = ' '.join(file_content.split())
        return file_content

    def generate_xaml(self):
        xaml_content = f"""
        <!-- XAML content for the basic activity: {self.activity_name} -->
        <!-- Example: Some activity content -->
        """
        return xaml_content


    def generate_assign_activity(self, assign_data):
        xaml = f"<Assign>{assign_data}</Assign>"
        return xaml

    def generate_flow_decision_activity(self, condition):
        xaml = f"<FlowDecision>{condition}</FlowDecision>"
        return xaml

    def add_variables_to_sequence(self, sequence_xaml, variables):
        for variable in variables:
            variable_name = variable['name']
            variable_type = variable['type']
            sequence_xaml += f"<Variable Type=\"{variable_type}\">{variable_name}</Variable>\n"

        return sequence_xaml

    def generate_argument(self, arg_name, arg_type, arg_data_type):
        if arg_type == 'in':
            return f"<Argument Direction=\"In\" Name=\"{arg_name}\" Type=\"{arg_data_type}\" />"
        elif arg_type == 'out':
            return f"<Argument Direction=\"Out\" Name=\"{arg_name}\" Type=\"{arg_data_type}\" />"
        elif arg_type == 'in/out':
            return f"<Argument Direction=\"InOut\" Name=\"{arg_name}\" Type=\"{arg_data_type}\" />"
        else:
            raise ValueError("Invalid argument type. Must be 'in', 'out', or 'in/out'.")

    def get_activities(self, variables, arguments=None):
        activities_list = []
        sequence_xaml = ""  # Initialize an empty sequence XAML

        for activity_data in self.activities_data:
            activity_type = activity_data.get('type')
            if activity_type == 'Assign':
                assign_data = activity_data.get('data')
                xaml = self.generate_assign_activity(assign_data)
                sequence_xaml += xaml
            elif activity_type == 'FlowDecision':
                condition = activity_data.get('condition')
                xaml = self.generate_flow_decision_activity(condition)
                sequence_xaml += xaml
         # Add variables to the sequence XAML
        sequence_xaml_with_variables = self.add_variables_to_sequence(sequence_xaml, variables)
        activities_list.append(sequence_xaml_with_variables)

        if arguments:
            for arg_name, arg_info in arguments.items():
                arg_type = arg_info['type']
                arg_data_type = arg_info.get('data_type', '')  # Get data type or default to empty string
                argument_xaml = self.generate_argument(arg_name, arg_type, arg_data_type)
                activities_list.append(argument_xaml)

        return activities_list