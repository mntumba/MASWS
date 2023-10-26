import sys

def generate_promela_model(requirements):
    promela_model = ""

    num_agents = 0
    num_resources = 0

    agents_index = requirements.index("agents:") + 1
    if agents_index < len(requirements):
        for requirement in requirements[agents_index:]:
            if requirement == "":
                break
            num_agents += 1
    
    resources_index = requirements.index("resources:") + 1
    if resources_index < len(requirements):
        for requirement in requirements[resources_index:]:
            if requirement == "":
                break
            num_resources += 1
    
    demands = []
    access_resources = []

    for agent in range(1, num_agents + 1):
        demand_index = requirements.index("a" + str(agent) + ":") + 1
        demand = requirements[demand_index].split()
        if len(demand) >= 2:
            demands.append(demand[1])

        access_index = requirements.index("a" + str(agent) + ":") + 2
        agent_access = []
        for requirement in requirements[access_index + 1:]:
            if requirement == "":
                break
            agent_access.append(requirement[-1])
        
        access_resources.append(agent_access)
    
    agent_demands = []
    demand_controllers = []
    agent_states = []
    agent_accesses = []
    for agent in range(1, num_agents + 1):
        agent_demands.append(f"""
    #define A{agent}_DEMAND {demands[agent - 1]}""")
        demand_controllers.append(f"""
    int agent{agent}_demand = 0;""")
        agent_states.append(f"""
    mtype agent{agent}_state = IDLE;""")
        agent_accesses.append(f"""
    int agent{agent}_access[{len(access_resources[agent - 1])}] = {{{', '.join(access for access in access_resources[agent - 1])}}};""")
    

    process_runs = []
    agent_demand_handlers = []
    processes = []
    resource_usage = []
    winning_strategy = f"""(([] <> (agent1_state == WORKING))"""
    handler = f"""              
        if"""
    for resource in range(1, num_resources + 1):
        resource_usage.append(f"""
    int resource{resource}_used_by = -1;""")
        handler += f"""
        ::requested_resource == {resource} && resource{resource}_used_by == -1 -> 
            if"""
        for agent in range(1, num_agents + 1):
            handler += f"""
            ::requesting_agent == {agent} && agent{agent}_demand < A{agent}_DEMAND ->
                resource{resource}_used_by = requesting_agent;
                agent{agent}_demand++;"""
        handler += f"""
            ::else ->
                a[requesting_agent].has_requested[requested_resource] = false;
            fi;"""

    for agent in range(1, num_agents + 1):
        if agent + 1 < num_agents + 1 :
            winning_strategy += f""" && ([] <> (agent{agent + 1}_state == WORKING))"""
        process_runs.append(f"""
            run Agent{agent}({agent});""")
        
    winning_strategy += f""")"""

    agent_demand_handlers.append(handler)

    for agent in range(1, num_agents + 1):
        process = f"""
    proctype Agent{agent}(int agent_id) {{
        do
            ::agent{agent}_state == IDLE ->
                agent{agent}_state = REQUESTING;
            ::agent{agent}_state == REQUESTING ->		
                do"""

        process_last = f"""
                    ::agent{agent}_demand == A{agent}_DEMAND"""

        for res in range(0, len(access_resources[agent - 1])):
            process += f"""
                    ::resource{access_resources[agent - 1][res]}_used_by == -1 && !a[agent_id].has_requested[agent{agent}_access[{res}]] && agent{agent}_demand < A{agent}_DEMAND ->
                        a[agent_id].has_requested[agent{agent}_access[{res}]] = true;
                        request_chan[agent{agent}_access[{res}]] ! agent_id, agent{agent}_access[{res}];
            """
        
        process += process_last
        process += f""" ->
                        agent{agent}_state = WORKING;
                        break;
                od
            ::agent{agent}_state == WORKING ->
                delay();
                agent{agent}_state = RELEASING;
            ::agent{agent}_state == RELEASING ->
                atomic {{
                    do"""

        for res in range(0, len(access_resources[agent - 1])):
                process += f"""
                    ::resource{access_resources[agent - 1][res]}_used_by == agent_id ->
                        resource{access_resources[agent - 1][res]}_used_by = -1
                        agent{agent}_demand--;
                        a[agent_id].has_requested[agent{agent}_access[{res}]] = false;"""                  
                	

        process += f"""
                    ::agent{agent}_demand == 0 ->		    
                        agent{agent}_state = IDLE;
                        break;
                    od
                }}
        od;
    }}\n"""


        processes.append(process)         
                        

    # Define the Promela template for requirements
    requirement_template = f"""
    #define NUM_AGENTS {num_agents}
    #define NUM_RESOURCES {num_resources}
    {''.join(demand for demand in agent_demands)}

    #define DELAY 0

    mtype = {{ IDLE, REQUESTING, WORKING, RELEASING }};
    int resource_used_by[NUM_RESOURCES + 1];
    chan request_chan[NUM_RESOURCES + 1] = [NUM_RESOURCES + 1] of {{ int, int }};
    {''.join(demand for demand in demand_controllers)}
    {''.join(state for state in agent_states)}
    {''.join(access for access in agent_accesses)}
    {''.join(res for res in resource_usage)}

    typedef agent {{
        bool has_requested[NUM_RESOURCES + 1];
    }};

    agent a[NUM_AGENTS + 1];

    inline resolve_conflicts(resource_id) {{
        int j;
        int chan_len = len(request_chan[resource_id])
        for (j : 0 .. chan_len - 1) {{
            request_chan[resource_id]?requesting_agent, requested_resource;
            a[requesting_agent].has_requested[requested_resource] = false;
        }}
    }}

    inline handle_allocation(resource_id) {{
        request_chan[resource_id]?requesting_agent, requested_resource;{''.join(handler for handler in agent_demand_handlers)}
        ::else ->
            a[requesting_agent].has_requested[requested_resource] = false;
        fi;
    }}

    inline delay() {{
        int i;
        for (i : 0 .. DELAY) {{
            skip;
        }}
    }}

    {''.join(process for process in processes)}
    
    proctype Environment() {{
        int requesting_agent;
        int requested_resource;
        int requesting_agent_demand;
        int i;
        do
        ::
            for (i : 1 .. NUM_RESOURCES) {{
                if
                    ::len(request_chan[i]) == 1 -> handle_allocation(i);
                    ::len(request_chan[i]) > 1 -> resolve_conflicts(i);
                    ::else -> skip;	
                fi;
            }}
        od;
    }}

    init {{
        atomic {{      
	    {''.join(proc for proc in process_runs)}
            run Environment();
        }}
    }}

    ltl existential {{ {winning_strategy} }}
    ltl universal {{ { "!" + winning_strategy } }}

    """

    # Add the requirement template to the Promela model
    promela_model += requirement_template


    return promela_model

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python generate_promela_model.py <input_file>")
        sys.exit(1)

    input_file = sys.argv[1]

    with open(input_file, "r") as file:
        requirements = [line.strip() for line in file.readlines()]

    promela_code = generate_promela_model(requirements)

    # Print or save the generated Promela model to a file
    print(promela_code)
