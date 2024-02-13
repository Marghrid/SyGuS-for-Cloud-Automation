import csv
import glob
import json
import re

import matplotlib.pyplot as plt

from synthesizer.util import human_time, Solution, SynthesisSolver


def make_csv_tables(results_table_filename: str, comparison_table_filename: str):
    results_rows = []
    for file in glob.glob('data_synthesis_solutions/*.json'):
        with open(file, 'r') as f:
            solutions = json.load(f)
        for sol in solutions:
            assert sol is not None, file
            row = {
                'instance name': sol["instance"],
                'function name': sol["name"],
                'depth': sol["depth"],
                'solver': sol['solver'],
                'solution': sol["solution"],
                'solve time': sol["solve time"]
            }
            results_rows.append(row)

    results_rows = sorted(results_rows, key=lambda r: (r['instance name'], r['function name'], r['solver']))
    with open(results_table_filename, 'w') as f:
        writer = csv.DictWriter(f, fieldnames=results_rows[0].keys())
        writer.writeheader()
        writer.writerows(results_rows)

    instances = set((row['instance name'], row['function name']) for row in results_rows)
    solver_comparison_rows = []
    for instance in instances:
        solver_comparison_row = {'instance name': instance[0], 'function name': instance[1]}
        is_sat = False
        is_unsat = False
        for solver in map(lambda s: s.name, SynthesisSolver):
            instance_solver_solutions = tuple(
                filter(lambda r: r['instance name'] == instance[0] and
                                 r['function name'] == instance[1] and
                                 r['solver'] == solver,
                       results_rows))
            if len(instance_solver_solutions) == 1:
                sol = instance_solver_solutions[0]
            elif len(instance_solver_solutions) > 1:
                sol = min(instance_solver_solutions,
                          key=lambda s: float(s['solve time']))
            else:
                sol = {'solution': '-', 'solve time': '-'}

            if 'unsat' in sol['solution']:
                is_unsat = True
            elif sol['solution'] != '-' and 'timeout' not in sol['solution']:
                is_sat = True
            if is_sat and is_unsat:
                print(f'Warning: {instance[0]}::{instance[1]} is both sat and unsat.')
            solver_comparison_row[f'{solver} solution'] = sol["solution"]
            solver_comparison_row[f'{solver} solve time'] = sol["solve time"]
        solver_comparison_rows.append(solver_comparison_row)

    solver_comparison_rows = sorted(solver_comparison_rows,
                                    key=lambda r: (r['instance name'], r['function name']))
    with open(comparison_table_filename, 'w') as f:
        writer = csv.DictWriter(f, fieldnames=solver_comparison_rows[0].keys())
        writer.writeheader()
        writer.writerows(solver_comparison_rows)


def to_latex(s: str) -> str:
    r = (s.replace('_', '\\_').replace('$', '\\$')
         .replace('#', '\\#').replace('%', '\\%')
         .replace('! ', '!').replace('<', '$<$'))
    return r


def get_instance_name(result):
    return f'{result['instance name']}::{result['function name']}'


def make_latex_instances_table(all_solutions):
    # build the instances dict
    instances_dict = {}
    rosette_unsats = set()
    cvc5_timeouts = set()
    for result in all_solutions:
        instance_name = get_instance_name(result)

        if result['solver'] == 'Rosette' and 'unsat' in result['solution']:
            rosette_unsats.add(instance_name)
        if result['solver'] == 'CVC5' and 'timeout' in result['solution']:
            cvc5_timeouts.add(instance_name)

        if instance_name not in instances_dict:
            instances_dict[instance_name] = result['solution']
        else:
            if 'timeout' in instances_dict[instance_name]:
                # if instance_name in cvc5_timeouts and 'timeout' not in result['solution']:
                #     cvc5_timeouts.remove(instance_name)
                instances_dict[instance_name] = result['solution']
            elif ('unsat' in instances_dict[instance_name] and
                  'unsat' in result['solution']):
                # Both are UNSAT, keep the most general UNSAT
                if instances_dict[instance_name] == '(unsat)' or result['solution'] == '(unsat)':
                    # One of the unsats does not have a depth, keep that one
                    instances_dict[instance_name] = '(unsat)'
                else:
                    # Else keep the one with the highest depth
                    depth_old = int(re.fullmatch(r'\(unsat d=(\d+)\)', instances_dict[instance_name]).groups()[0])
                    depth_new = int(re.fullmatch(r'\(unsat d=(\d+)\)', result['solution']).groups()[0])
                    if depth_new > depth_old:
                        instances_dict[instance_name] = result['solution']

            elif ('unsat' not in result['solution'] and
                  'timeout' not in result['solution']
                  and instances_dict[instance_name] != result['solution']):
                print(f'Warning: {instance_name} has different solutions: '
                      f'{instances_dict[instance_name]} and {result['solution']}')
                if len(result['solution']) < len(instances_dict[instance_name]) or \
                        (len(result['solution']) == len(instances_dict[instance_name]) and
                         result["solution"] < instances_dict[instance_name]):
                    instances_dict[instance_name] = result['solution']

    print('\n\n\n\n============\n\n\n\n')

    title_format = r'\bf\large'

    table_str = r'''\begin{table*}[t]
\centering\small
\begin{tabular}{@{}rl@{}}

'''
    table_str += (fr'{title_format} \# & '
                  # fr'{title_format} Instance name & '
                  fr'{title_format} synthesized function \\\hline') + '\n'
    for idx, instance in enumerate(instances_dict):  # sorted(instances_dict, key=instances_dict.get):
        if 'timeout' in instances_dict[instance] or 'unsat' in instances_dict[instance]:
            continue

        cellcolor = ''
        if instance in cvc5_timeouts:
            cellcolor = r'\cellcolor{cyan!20}'
        elif instance in rosette_unsats:
            cellcolor = r'\cellcolor{purple}\color{white}'
        text = (fr'{cellcolor}{idx} & ' +
                # fr'{cellcolor}\texttt{{{to_latex(instance)}}} & ' +
                fr'{cellcolor}\texttt{{{to_latex(instances_dict[instance])}}} \\')
        table_str += text + '\n'

    table_str += r'''\end{tabular}
\caption{Satisfiable synthesis instances and their synthesized functions solutions. 
Highlighted in \colorbox{purple}{\textcolor{white}{purple}} are 2 instances for which Rosette's 
most general answer is UNSAT for d=3, but CVC5 is able to find an answer. 
In \colorbox{cyan!20}{cyan}, the 4 instances that were solved by Rosette but timed out in CVC5.
The remaining 16 instances got a SAT response from both solvers.
} 
\label{tab:instances-table}
\end{table*}

'''
    print(table_str)

    with open('instances_table.tex', 'w') as f:
        f.write(table_str)


def make_latex_solver_comparison_tables(all_solutions):
    solver_comparison_dict = {}
    for solver in map(lambda s: s.name, SynthesisSolver):
        solver_comparison_dict[solver] = {}
    for solution in all_solutions:
        instance_name = f'{solution["instance name"]}::{solution["function name"]}'
        solver = solution['solver']
        if instance_name not in solver_comparison_dict[solver]:
            solver_comparison_dict[solver][instance_name] = solution['solution'], solution['solve time']
        else:
            this_solution = solution['solution']
            stored_solution = solver_comparison_dict[solver][instance_name][0]
            if 'timeout' in stored_solution:
                solver_comparison_dict[solver][instance_name] = this_solution, solution['solve time']
            elif ('unsat' in stored_solution and 'unsat' in this_solution):
                if this_solution == '(unsat)':
                    solver_comparison_dict[solver][instance_name] = this_solution, solution['solve time']
                else:
                    depth_old = int(re.fullmatch(r'\(unsat d=(\d+)\)', stored_solution).groups()[0])
                    depth_new = int(re.fullmatch(r'\(unsat d=(\d+)\)', this_solution).groups()[0])
                    if depth_new > depth_old:
                        solver_comparison_dict[solver][instance_name] = this_solution, solution['solve time']

            elif ('unsat' not in this_solution and
                  'timeout' not in this_solution
                  and stored_solution != this_solution):
                print(f'Warning: {instance_name} has different solutions: '
                      f'{stored_solution} and {solution["solution"]}')
                if len(solution["solution"]) < len(stored_solution) or \
                        (len(solution["solution"]) == len(stored_solution) and
                         solution["solution"] < stored_solution):
                    solver_comparison_dict[solver][instance_name] = this_solution, solution['solve time']

    all_names = set(map(get_instance_name, all_solutions))
    for instance in all_names:
        for solver in solver_comparison_dict:
            assert instance in solver_comparison_dict[solver], f'{instance} not in {solver}'

    print('\n\n\n\n============\n\n\n\n')

    # print(r'\definecolor{lightred}{rgb}{1, 0.85, 0.85}')
    title_format = r'\bf\large'
    table_str = r'''\begin{table}[t]
\begin{minipage}{.48\linewidth}\centering\small
\begin{tabular}{@{}rcc@{}}

'''
    table_str += (rf' {title_format} \# & '
                  # rf'{title_format} Instance name & '
                  rf'{title_format} Rosette& '
                  rf'{title_format} CVC5\\\hline') + '\n'

    unsat_sat_points = []
    sat_sat_points = []
    unsat_unsat_points = []
    for idx, instance in enumerate(sorted(all_names)):

        if 'timeout' in solver_comparison_dict['CVC5'][instance][0]:
            continue
        elif ('unsat' in solver_comparison_dict['Rosette'][instance][0] and
                'unsat' not in solver_comparison_dict['CVC5'][instance][0]):
            cell_color = r'\cellcolor{purple}\color{white}'
            unsat_sat_points.append((solver_comparison_dict['Rosette'][instance][1],
                                      solver_comparison_dict['CVC5'][instance][1]))
        elif 'unsat' in solver_comparison_dict['Rosette'][instance][0] and 'unsat' in \
                solver_comparison_dict['CVC5'][instance][0]:
            cell_color = r'\cellcolor{Apricot}'
            unsat_unsat_points.append((solver_comparison_dict['Rosette'][instance][1],
                                        solver_comparison_dict['CVC5'][instance][1]))
        else:
            cell_color = ''
            sat_sat_points.append((solver_comparison_dict['Rosette'][instance][1],
                                  solver_comparison_dict['CVC5'][instance][1]))
        text = (cell_color + fr'{idx} & ' +
                # cell_color + fr'\texttt{{{to_latex(instance)}}} & ' +
                cell_color + fr'{to_latex(human_time(solver_comparison_dict['Rosette'][instance][1]))} & ' +
                cell_color + fr'{to_latex(human_time(solver_comparison_dict['CVC5'][instance][1]))} \\')
        table_str += text + '\n'

    table_str += r'''\end{tabular}
\caption{Solve time using Rosette vs. CVC5 for instances for which both produced a solution (excluding CVC5 timeouts). 
11 Rosette UNSATs confirmed UNSAT for all depths by CVC5 are highlighted in \colorbox{Apricot}{apricot}. 
2 instances for which Rosette's most general answer is UNSAT for d=3, but for which CVC5 is able to find an answer 
are shaded in \colorbox{purple}{\textcolor{white}{purple}}. 
The remaining 16 instances got a SAT response from both solvers.
}
\label{tab:solved-instances-time-table}
\end{minipage} \hfill
'''

    # print(table_str)
    # with open('solve_times_comparison_table.tex', 'w') as f:
    #     f.write(table_str)

    # print('\n\n\n\n============\n\n\n\n')

    # print(r'\definecolor{lightred}{rgb}{1, 0.85, 0.85}')
    title_format = r'\bf\large'
    table_str += r'''\begin{minipage}{.48\linewidth}\centering\small
\begin{tabular}{@{}rc@{}}
'''
    table_str += (rf' {title_format} \# & '
                  # rf'{title_format} Instance name & '
                  rf'{title_format} Rosette\\\hline') + '\n'
    sat_timeout_points = []
    unsat_timeout_points = []
    ds = [2, 3, 5, 6, 7, 9]
    for idx, instance in enumerate(sorted(all_names)):
        cell_color = ''
        if 'timeout' not in solver_comparison_dict['CVC5'][instance][0]:
            continue
        if 'unsat' in solver_comparison_dict['Rosette'][instance][0]:
            unsat_timeout_points.append(
                (solver_comparison_dict['Rosette'][instance][1], solver_comparison_dict['CVC5'][instance][1]))

            d = int(re.fullmatch(r'\(unsat d=(\d+)\)', solver_comparison_dict['Rosette'][instance][0]).groups()[0])

            di = ds.index(d) + 1
            if di < 4:
                cell_color = rf'\cellcolor{{MidnightBlue!{int(di * 16)}}}'
            else:
                cell_color = rf'\cellcolor{{MidnightBlue!{int(di * 16)}}}\color{{white}}'
        else:
            sat_timeout_points.append(
                (solver_comparison_dict['Rosette'][instance][1], solver_comparison_dict['CVC5'][instance][1]))

        text = (cell_color + fr'{idx} & ' +
                # cell_color + fr'\texttt{{{to_latex(instance)}}} & ' +
                cell_color + fr'{to_latex(human_time(solver_comparison_dict['Rosette'][instance][1]))} \\')
        table_str += text + '\n'

    table_str += r'''\end{tabular}
\caption{Solve time using Rosette for instances that CVC5 timed out after 5 minutes.
Instances highlighted in shades of \colorbox{MidnightBlue}{\textcolor{white}{midnight blue}} 
show the instances for which Rosette's best solution is UNSAT. 
Darker shades indicate that Rosette was able to show unsatisfiability for a higher depth.
% The solve time for an instance with UNSAT proved for a higher depth does not include the time taken 
% to prove UNSAT to lower depths before, as these calls are all done in parallel.
}
\label{tab:solve-time-cvc5-timeouts-table}
\end{minipage}
\end{table}
'''

    print(table_str)
    with open('solver_times_table.tex', 'w') as f:
        f.write(table_str)

    plt.title('Solve time using Rosette vs. CVC5', fontsize=16)
    plt.scatter(*zip(*sat_sat_points), label='Rosette SAT, CVC5 SAT', color='grey', marker='^')
    plt.scatter(*zip(*unsat_sat_points), label='Rosette UNSAT, CVC5 SAT', color='purple', marker='*')
    plt.scatter(*zip(*unsat_unsat_points), label='Rosette UNSAT, CVC5 UNSAT', color='orange', marker='v')
    plt.scatter(*zip(*sat_timeout_points), label='Rosette SAT, CVC5 timeout', color='black', marker='x')
    plt.scatter(*zip(*unsat_timeout_points), label='Rosette UNSAT, CVC5 timeout', color='red', marker='2')
    plt.plot([0, 500], [0, 500], label='y=x', color='lightgrey', linestyle='--')
    plt.xlabel('Rosette solve time (s)', fontsize=14)
    plt.ylabel('CVC5 solve time (s)', fontsize=14)
    plt.xscale('log')
    plt.yscale('log')
    plt.xlim(0.01, 500)
    plt.ylim(0.01, 500)
    plt.legend()
    plt.savefig('solve_times_comparison_scatter.pdf', bbox_inches='tight')
    plt.show()



def get_all_solutions():
    all_solutions: list[Solution] = []
    for file in glob.glob('data_synthesis_solutions/*.json'):
        with open(file, 'r') as f:
            file_solutions = json.load(f)
        for sol in file_solutions:
            assert sol is not None, file
            row = {
                'instance name': sol['instance'],
                'function name': sol['name'],
                'depth': sol['depth'],
                'solver': sol['solver'],
                'solution': sol['solution'],
                'solve time': sol['solve time']
            }
            all_solutions.append(row)

            if sol['solver'] == 'Rosette' and 'timeout' in sol['solution']:
                print(f'Rosette timeout', len(sol['keys']), len(sol['values']))
            elif sol['solver'] == 'CVC5' and 'timeout' in sol['solution']:
                print(f'CVC5 timeout', len(sol['keys']), len(sol['values']))

    all_solutions = sorted(all_solutions, key=lambda r: (r['instance name'], r['function name'], r['solver']))
    return all_solutions


def make_heatmap_with_solutions_distribution(all_solutions):
    instance_names = set(map(get_instance_name, all_solutions))
    solver_comparison_dict = {}
    for solver in map(lambda s: s.name, SynthesisSolver):
        solver_comparison_dict[solver] = {}
    for solution in all_solutions:
        instance_name = f'{solution["instance name"]}::{solution["function name"]}'
        solver = solution['solver']
        if instance_name not in solver_comparison_dict[solver]:
            solver_comparison_dict[solver][instance_name] = solution['solution'], solution['solve time']
        else:
            this_solution = solution['solution']
            stored_solution = solver_comparison_dict[solver][instance_name][0]
            if 'timeout' in stored_solution:
                solver_comparison_dict[solver][instance_name] = this_solution, solution['solve time']
            elif ('unsat' in stored_solution and 'unsat' in this_solution):
                if this_solution == '(unsat)':
                    solver_comparison_dict[solver][instance_name] = this_solution, solution['solve time']
                else:
                    depth_old = int(re.fullmatch(r'\(unsat d=(\d+)\)', stored_solution).groups()[0])
                    depth_new = int(re.fullmatch(r'\(unsat d=(\d+)\)', this_solution).groups()[0])
                    if depth_new > depth_old:
                        solver_comparison_dict[solver][instance_name] = this_solution, solution['solve time']

            elif ('unsat' not in this_solution and
                  'timeout' not in this_solution
                  and stored_solution != this_solution):
                print(f'Warning: {instance_name} has different solutions: '
                      f'{stored_solution} and {solution["solution"]}')
                if len(solution["solution"]) < len(stored_solution) or \
                        (len(solution["solution"]) == len(stored_solution) and
                         solution["solution"] < stored_solution):
                    solver_comparison_dict[solver][instance_name] = this_solution, solution['solve time']

    all_names = set(map(get_instance_name, all_solutions))
    for instance in all_names:
        for solver in solver_comparison_dict:
            assert instance in solver_comparison_dict[solver], f'{instance} not in {solver}'

    # SAT = 0
    # UNSAT = 1
    # TIMEOUT = 2
    # Rosette is the columns, CVC5 is the rows

    matrix_solution = {}

    for instance in all_names:
        if 'timeout' in solver_comparison_dict['CVC5'][instance][0]:
            row = 'T/O'
        elif 'unsat' in solver_comparison_dict['CVC5'][instance][0]:
            row = 'UNSAT'
        else:
            row = 'SAT'

        if 'timeout' in solver_comparison_dict['Rosette'][instance][0]:
            col = 'T/O'
        elif 'unsat' in solver_comparison_dict['Rosette'][instance][0]:
            m = re.fullmatch(r'\(unsat d=(\d+)\)',
                             solver_comparison_dict['Rosette'][instance][0])
            if m is None:
                print('ERROR', solver_comparison_dict['Rosette'][instance][0])
                continue
            d = int(m.groups()[0])
            col = f'UNSAT\n(d={d})'
        else:
            col = 'SAT'

        matrix_solution[instance] = (row, col)

    rows = sorted({matrix_solution[instance][0] for instance in matrix_solution})
    rows.remove('T/O')
    rows.append('T/O')
    cols = sorted({matrix_solution[instance][1] for instance in matrix_solution})

    matrix = [[0 for _ in cols] for _ in rows]
    for instance in matrix_solution:
        row = rows.index(matrix_solution[instance][0])
        col = cols.index(matrix_solution[instance][1])
        matrix[row][col] += 1

    plt.text((len(cols) - 1) / 2, -1.5, 'Rosette output', ha='center', va='center', color='black', fontsize=22)
    plt.text(-1.3, (len(rows) - 1) / 2, 'CVC5 output', ha='center', va='center', color='black', fontsize=22,
             rotation=90)

    for i in range(len(rows)):
        for j in range(len(cols)):
            if matrix[i][j] > .5 * max(matrix[ii][jj] for ii in range(len(rows)) for jj in range(len(cols))):
                color = 'white'
            else:
                color = 'black'
            plt.text(j, i, f'{matrix[i][j]}',
                     ha='center', va='center', color=color, fontsize=16)

    plt.imshow(matrix, cmap='Blues')
    plt.xticks(range(len(cols)), cols, fontsize=14)
    plt.yticks(range(len(rows)), rows, rotation=90, va='center', fontsize=14)
    plt.tick_params(length=0, labeltop=True, labelbottom=False)
    plt.savefig('solution_distribution.pdf', bbox_inches='tight')
    plt.show()


if __name__ == '__main__':
    # instances_dir_name = instances_dir.replace('resources', '').replace('/', '')
    # make_csv_tables(f'results_{instances_dir_name}.csv', f'solver_comparison_{instances_dir_name}.csv')

    all_solutions = get_all_solutions()
    make_latex_instances_table(all_solutions)
    make_latex_solver_comparison_tables(all_solutions)
    make_heatmap_with_solutions_distribution(all_solutions)
