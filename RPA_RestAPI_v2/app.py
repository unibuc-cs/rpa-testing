import json
import xml.etree.ElementTree as ET
from flowchart_generator import generate_flowchart
from sequence_generator import generate_sequence
from excel_reader import generate_read_range
from flowchart_condition_generator import generate_flowchart_with_condition
from simpleBankLoanCSharp_generator import generateBankLoanCSharp
from ActivitiesClass import Activities
from GraphClass import Graph

from flask import Flask, jsonify, abort, request, make_response, url_for

app = Flask(__name__)

# Example route for generating .xaml files
#@app.route('/generate_xaml', methods=['POST']) #accept post requests at this route
#def generate_xaml():
    # receive some data in the request
 #   data = request.json
  #  xaml_content = generate_flowchart()

   # response = jsonify({'xaml_content': xaml_content})

    # Respond with the generated .xaml content
    #print(json.dumps(response.json, indent=4))

    #return response
   # return jsonify({'xaml_content': file_content})

@app.route('/generate_flowchart', methods=['GET'])
def generate_flowchart_route():
    file_content = generate_flowchart()
    return jsonify({'xaml_content': file_content})

@app.route('/generate_sequence', methods=['GET'])
def generate_sequence_route():
    file_content = generate_sequence()
    return jsonify({'xaml_content': file_content})

activity_name = "ReadExcelActivity"
file_path = "excel_reader_test.xlsx"
sheet_name = "Sheet1"
output_variable = "DataTableOutput"

@app.route('/generate_excel_reader', methods=['GET'])
def generate_excel_reader_route():
    file_content = generate_read_range(activity_name, file_path, sheet_name, output_variable)
    return jsonify({'xaml_content': file_content})

@app.route('/generate_flowchart_with_condition_route', methods=['GET'])
def generate_flowchart_with_condition_route():
    activity_name = "MyFlowchart"
    loan = 800
    term = 12
    file_content = generate_flowchart_with_condition(activity_name,loan,term)
    return jsonify({'xaml_content': file_content})


@app.route('/generate_simpleBankLoanCSharp_route', methods=['GET'])
def generate_simple_bank_loan_route():
    local_number_retries = 3
    local_pin_test = "1234"
    expected_pin = "1111"
    actual_pin_values =""
    out_pin_check_successful = ""
    file_content = generateBankLoanCSharp(local_number_retries,local_pin_test,expected_pin,actual_pin_values,out_pin_check_successful)
    return jsonify({'xaml_content': file_content})

@app.route('/generate_xaml', methods=['GET'])
def generate_xaml():
    # Example usage: Create basic activities
    activity1 = Activities("Activity1")
    activity2 = Activities("Activity2")

    # Create a graph and add activities
    graph = Graph()
    graph.add_activity(activity1)
    graph.add_activity(activity2)

    # Generate XAML content for the graph
    xaml_content = graph.generate_xaml()

    # Construct the response
    response = {
        "xaml_content": xaml_content
    }

    return jsonify(response)

@app.route('/generate_banlloanpin', methods=['GET'])
def generate_bankloanpin():
    main_activity = Activities('MainActivity')
    invoked_activity = Activities('InvokedActivity')
    local_number_retries = 3
    local_pin_test = "1234"
    expected_pin = "1111"
    actual_pin_values = ""
    out_pin_check_successful = ""
    loan = 800
    term = 5
    loan_type = ""
    term_type = ""
    obtained_result = ""
    pin_check_successful = ""
    invoked_content = invoked_activity.generate_flowchart_pin(local_number_retries,local_pin_test,expected_pin,actual_pin_values,out_pin_check_successful)
    main_content = main_activity.generate_flowchart_main(loan_type, term_type, obtained_result, pin_check_successful, loan, term)
    response = {
        "main_content":main_content,
        "invoked_content": invoked_content
    }
    return jsonify(response)


@app.route('/combine', methods=['POST'])
def combine():
    data = request.json

    # 'graph_data' and 'activities_data' are present in the request
    graph_data = data.get('graph_data')
    activities_data = data.get('activities_data')
    variables_data = data.get('variables', [])
    arguments_data = data.get('arguments', {})  # Default to an empty dictionary if no arguments are provided

    variables = []
    for variable_info in variables_data:
        variables.append({
            'name': variable_info.get('name'),
            'type': variable_info.get('type')
        })

    arguments = {}
    for arg_name, arg_info in arguments_data.items():
        arg_type = arg_info.get('type')
        arg_data_type = arg_info.get('data_type')
        arguments[arg_name] = {'name': arg_name, 'type': arg_type, 'data_type': arg_data_type}

    activities = Activities(activities_data)
    activities_list = activities.get_activities(variables, arguments)

    graph = Graph(graph_data)
    xaml = graph.combine(activities_list)

    return jsonify({'xaml': xaml})


if __name__ == '__main__':
    app.run(debug=True)