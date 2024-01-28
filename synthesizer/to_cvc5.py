import os
import subprocess
from collections import deque
from typing import Any

from synthesizer.to_synthesis import get_start_symbol
from synthesizer.util import human_time


def get_cvc5_list(lst: list[Any]):
    if len(lst) == 0:
        return 'j_nil_list'
    else:
        return f'(list_cons {to_cvc5_json_type(lst[0])} {get_cvc5_list(lst[1:])})'


def get_cvc5_dict(dct: dict[str, Any] or list[str, Any]):
    if len(dct) == 0:
        return 'j_nil_dict'
    else:
        if isinstance(dct, dict):
            ldict = list(sorted(dct.items(), key=lambda x: x[0]))
        else:
            ldict = dct
        key_str = '"' + ldict[0][0].replace('"', '\\"') + '"'
        return (f'(dict_cons {key_str} {to_cvc5_json_type(ldict[0][1])} '
                f'{get_cvc5_dict(ldict[1:])})')


def to_cvc5_json_type(i: Any) -> str:
    if isinstance(i, bool):
        return f'(jB {str(i).lower()})'
    if isinstance(i, str):
        return '(jS "' + i.replace('"', '\"') + '")'
    if isinstance(i, int) or isinstance(i, float):
        return f'(jI {i})'
    if i is None:
        return "jNull"
    if isinstance(i, list):
        return f'(jL {get_cvc5_list(i)})'
    if isinstance(i, dict):
        return f'(jD {get_cvc5_dict(i)})'

    raise NotImplementedError(f'to_cvc5 not implemented for {i.__class__.__name__}')


def to_cvc5(i: Any) -> str:
    if isinstance(i, bool):
        return f'{str(i).lower()}'
    if isinstance(i, str):
        return '"' + i.replace('"', '\\"') + '"'
    if isinstance(i, int) or isinstance(i, float):
        return f'{i}'
    if i is None:
        return "jNull"
    if isinstance(i, list):
        return f'{get_cvc5_list(i)}'
    if isinstance(i, dict):
        return f'{get_cvc5_dict(i)}'

    raise NotImplementedError(f'to_cvc5 not implemented for {i.__class__.__name__}')


def cvc5_file_preamble():
    with open(f'{os.getcwd()}/resources/synthesis/synthesis_lang.smt') as f:
        return f.read() + '\n\n'


def build_sygus_grammar(keys, indices, values, start_symb: str, synt_f_name: str = 'f0'):
    keys_str = ' '.join(f'"{k}"' for k in keys)
    values_str = ' '.join(to_cvc5_json_type(v) for v in values)
    indices_str = ' '.join(map(str, indices))

    if start_symb == 'SyntJ':
        start_type = 'Json'
    elif start_symb == 'SyntBool':
        start_type = 'Bool'
    else:
        raise NotImplementedError(f'Unknown type for start symbol {start_symb}')

    non_terminals = {}
    synth_bool_definition = """
    (SyntBool Bool (
      (is_empty SyntJ)
      (not SyntBool)"""
    if len(values) > 0:
        synth_bool_definition += '\n      (= SyntJ SySV)'
    synth_bool_definition += '\n    ))'
    non_terminals['(SyntBool Bool)'] = synth_bool_definition

    synth_json_defintion = """
   (SyntJ Json (
      (get_idx_list x SyntInt)"""
    if len(keys) > 0:
        synth_json_defintion += f"""
    (get_val_dict SyntJ SySK)
    (get_descendants_named SyntJ SySK)"""

    synth_json_defintion += "\n      (get_idx_list SyntJ SyntInt)"
    synth_json_defintion += "\n   ))"

    non_terminals['(SyntJ Json)'] = synth_json_defintion

    if len(keys) > 0:
        non_terminals['(SySK String)'] = f'\n    (SySK String ({keys_str}))'

    if len(values) > 0:
        non_terminals['(SySV Json)'] = f'\n    (SySV Json ({values_str}))'

    non_terminals['(SyntInt Int)'] = f'''\n    (SyntInt Int (
      {indices_str}
      (length SyntJ)
    ))'''

    non_terminals_list = list(sorted(non_terminals.items()))
    start_symbol_pair = tuple(filter(lambda p: start_symb in p[0], non_terminals_list))
    assert len(start_symbol_pair) == 1, (f'Expected to find exactly one start symbol, but found {start_symbol_pair}.\n '
                                         f'Looking for {start_symb} in {non_terminals.keys()}')
    start_symbol_pair = start_symbol_pair[0]
    non_terminals_list.remove(start_symbol_pair)
    non_terminals_list.insert(0, start_symbol_pair)

    s = f"""
(synth-fun {synt_f_name} ((x Json)) {start_type}
  ;;Non terminals of the grammar
  ( """
    s += ' '.join(map(lambda p: p[0], non_terminals_list))
    s += """ )
  ;;Define the grammar
  ("""
    s += '\n  '.join(map(lambda p: p[1], non_terminals_list))
    s += '\n  )\n)\n'
    return s


def build_cvc5_samples(synt_decl):
    s = ''
    for io_idx, io in enumerate(synt_decl['constraints']):
        s += f'(define-const sample{io_idx} Json {to_cvc5_json_type(io["inputs"])})\n'
    s += '\n'
    return s


def build_cvc5_synthesis_query(synt_decl, start_symbol):
    asserts = []
    f_name = synt_decl["name"]
    for ctr_idx, ctr in enumerate(synt_decl["constraints"]):
        if start_symbol == 'SyntJ':
            output_str = to_cvc5_json_type(ctr["output"])
        else:
            output_str = to_cvc5(ctr["output"])
        asserts.append(f'(constraint (= ({f_name} sample{ctr_idx}) {output_str}))')

    asserts_str = '\n'.join(asserts)

    s = asserts_str
    s += '\n\n(check-synth)\n'
    return s


def to_python(arg):
    try:
        return eval(arg)
    except (NameError, SyntaxError) as e:
        try:
            return eval(arg.replace('true', 'True').replace('false', 'False'))
        except (NameError, SyntaxError) as e:
            return arg


def parse_cvc5_output_aux(tokens: deque):
    two_arg_functions = ['get_idx_list', '=', 'get_descendants_named', 'get_val_dict']
    one_arg_functions = ['not', 'empty', 'jI', 'jS', 'is_empty']
    token = tokens.popleft()
    if token[0] == '(':
        func_name = token[1:]
        if func_name in one_arg_functions:
            arg0 = parse_cvc5_output_aux(tokens)
            return (func_name, (arg0))
        elif func_name in two_arg_functions:
            arg0 = parse_cvc5_output_aux(tokens)
            arg1 = parse_cvc5_output_aux(tokens)
            return (func_name, (arg0, arg1))
        if func_name == 'choose':
            # ignore
            return parse_cvc5_output_aux(tokens)
    if 'x' in token:
        return 'x'
    if token[-1] == ')':
        return eval(token.replace(')', ''))

    raise NotImplementedError(f'Handle parsing {token}, {tokens}')


def parse_cvc5_output(solver_output: str):
    tokens = deque(solver_output.split())
    try:
        token = tokens.popleft()
    except IndexError:
        raise RuntimeError(f'Empty output from CVC5.')
    assert token == '(', f'removed {token} from {tokens}.'
    token = tokens.popleft()
    assert token == '(define-fun', f'removed {token} from {tokens}.'
    token = tokens.popleft()  # func name
    token = tokens.popleft()  # x
    token = tokens.popleft()  # x type, Json
    token = tokens.popleft()  # return type, start symb

    return parse_cvc5_output_aux(tokens)


def cvc5_to_jsonpath(ast):
    input_name = 'x'
    if isinstance(ast, tuple):
        f_name, f_args = ast

        if f_name == 'get_val_dict':
            a0, a1 = f_args
            return f'{cvc5_to_jsonpath(a0)}.{a1}'
        elif f_name == 'get_descendants_named':
            a0, a1 = f_args
            return f'{cvc5_to_jsonpath(a0)}..{a1}'
        elif f_name == 'get_idx_list':
            a0, a1 = f_args
            return f'{cvc5_to_jsonpath(a0)}[{a1}]'
        elif f_name == '=':
            a0, a1 = f_args
            return f'({cvc5_to_jsonpath(a0)} == {cvc5_to_jsonpath(a1)})'
        elif f_name == 'not':
            a0 = f_args
            return f'! ({cvc5_to_jsonpath(a0)})'
        elif f_name == 'is_empty':
            a0 = f_args
            return f'(len({cvc5_to_jsonpath(a0)}) == 0)'
        elif f_name == 'jI' or f_name == 'jS':
            a0 = f_args
            return f'{cvc5_to_jsonpath(a0)}'
        else:
            raise NotImplementedError(f'to_jsonpath not implemented for operation {f_name}.')
    elif ast == input_name:
        return '$'
    if isinstance(ast, str):
        return f'"{ast}"'
    else:
        return ast


def convert_cvc5_to_jsonpath(solver_output: str):
    ast = parse_cvc5_output(solver_output)
    return cvc5_to_jsonpath(ast)


def get_cvc5_query(indices, keys, synt_decl, values):
    cvc5_text = ''
    cvc5_text += cvc5_file_preamble()
    start_symbol = get_start_symbol(synt_decl['constraints'])
    start_symbol = start_symbol[0].upper() + start_symbol[1:]
    f_name = synt_decl["name"]
    cvc5_text += build_sygus_grammar(keys, indices, values, start_symbol, f_name)
    cvc5_text += build_cvc5_samples(synt_decl)
    cvc5_text += build_cvc5_synthesis_query(synt_decl, start_symbol)
    return cvc5_text


def run_cvc5_command(cvc5_filename: str, timeout: int) -> str:
    """
    Runs a pre-written CVC5 Sygus file and returns the solution, in our jsonpath format.
    :param cvc5_filename: The name of the file with the sygus problem
    :param timeout: Synthesis timeout in seconds
    :return: solution in jsonpath format
    """
    cvc5_command = ['timeout', '-k', str(timeout + 10), str(timeout + 1),
                    'cvc5', cvc5_filename]
    try:
        result = subprocess.run(cvc5_command, capture_output=True, text=True, timeout=timeout)

        if 'unsat' in result.stdout or 'infeasible' in result.stdout:
            cvc5_out = '(unsat)'
        elif 'error' in result.stdout or 'error' in result.stderr:
            raise RuntimeError(f'Error in CVC5 '
                               f'{" ".join(cvc5_command)}:\n'
                               f'stdout: {result.stdout}\n'
                               f'stderr: {result.stderr}')
        else:
            cvc5_out = "\n".join(result.stdout.split('\n'))
            try:
                cvc5_out = convert_cvc5_to_jsonpath(cvc5_out)
            except RuntimeError as e:
                raise RuntimeError(
                    f'Something wrong with racket output to '
                    f'{" ".join(cvc5_command)}:\n'
                    f'stdout: {result.stdout}\n{e}')
        if len(result.stderr) > 0:
            print('CVC5 call stderr:', result.stderr)
        return cvc5_out

    except subprocess.TimeoutExpired:
        return f'(timeout {human_time(timeout)})'
