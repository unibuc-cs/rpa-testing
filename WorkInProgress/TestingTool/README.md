Steps to configure and run TestingTool - only for Windows operation system:

0. Clone the following repository:
   https://github.com/unibuc-cs/rpa-testing
   
1. Install python 3.8.0

2. Install the packages

	pip install pip install z3-solver
	
	pip install py_expression_eval
	
	pip install networkx
	
	And
	
    pip install pygraphviz
	
	for which you will need to follow this steps: ( see this link: https://github.com/pygraphviz/pygraphviz/issues/163#issuecomment-698541913 )
	
		Step 1: Download and install Graphviz

		https://graphviz.gitlab.io/_pages/Download/Download_windows.html

		Step 2: Add below path to your PATH environment variable

		C:\Program Files (x86)\Graphviz2.38\bin

		Step 3: Re-open command line and activate venv

		venv\Scripts\activate

		Step 4: Download binaries for pygraphviz and install in active venv

		https://github.com/CristiFati/Prebuilt-Binaries/tree/master/PyGraphviz/v1.5/Graphviz-2.42.2

		In case of python 3.8

		pip install pygraphviz-1.5-cp38-cp38-win_amd64.whl


3. Set your paths in configuration file from TestingTool\Applications\Models\ConfigurationFile.

4. The project was build on UiPath Studio Pro 2021.4.4 version. 
   If an older version is wanted, then the project should be opened with that version
   and all the packages from project should be reinstalled (install the packages available for that older version of Studio).    

5. Set a test data queue in orchestrator to be able to run TestCaseWithQueue.xaml and make sure the name of the queue is also set in the configuration file. 
		
		To create a test data queue follow the following steps, as specified at https://docs.uipath.com/orchestrator/v0/docs/managing-test-data-queues-in-orchestrator:
		Step0: Create an account / login at: https://cloud.uipath.com/
		Step1: Navigate to Orchestrator -> Testing> Test Data Queues.
		Step2: Click Add test data queue.
		Step3: Enter a Name for your test data queue.
		Step4: Add an optional Description to help you easily identify the use of each test data queue.
		Step5: Click Browse to find and upload your JSON schema.
		
6. Go to TestingTool\Applications\Models

   and in order to see the test coverage, run one of the following in the debug mode:
   
   TestCase.xaml contains the testing of Create Loan Process - With Invoked Pin Check_v2.
   or
   TestCaseWithQueue.xaml contains the testing of Create Loan Process - With Invoked Pin Check_v2 using a test queue in orchestrator.
