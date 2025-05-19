# RPA and testing
RPA testing: test generation for UiPath RPA robots (see TestingToolStable folder from this repository)

Steps to configure and run TestingTool - only for Windows operation system:

0. Clone the following repository:
   https://github.com/unibuc-cs/rpa-testing
   
1. Install python 3.8.0

2. Install the packages

	pip install pip install z3-solver
	
	pip install py_expression_eval
	
	pip install networkx
	
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
3. The RPA modles that can be tested can be found in TestingToolStable -> Applications -> C#Models
4. In each RPA model's folder there are also examples of the necessary csv files for the model to be tested and also some output data from the previous runs.
Developed by [@unibuc-cs/rpa-testing](https://github.com/orgs/unibuc-cs/teams/rpa-testing)
