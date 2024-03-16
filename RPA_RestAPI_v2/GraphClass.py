class Graph:
    def __init__(self, graph_data):
        self.graph_data = graph_data

    def add_activity(self, activity):
        self.activities.append(activity)

    def combine(self, activities):
        # Generate XAML content for the graph incorporating activities
        xaml = "<Workflow>\n"
        for activity in activities:
            # Generate XAML code for each activity
            xaml += f"\t<Activity>{activity}</Activity>\n"

        xaml += "</Workflow>"
        return xaml