import subprocess
from collections import deque
from typing import Any

from synthesizer.to_synthesis import get_start_symbol, get_synthesis_strings
from synthesizer.util import get_timeout_command_prefix, human_time


def get_cvc5_list(lst: list[Any], str_to_cvc5_mapping: dict[str, str]) -> str:
    if len(lst) == 0:
        return 'j_nil_list'
    else:
        return (f'(list_cons {to_cvc5_json_type(lst[0], str_to_cvc5_mapping)} '
                f'{get_cvc5_list(lst[1:], str_to_cvc5_mapping)})')


def get_cvc5_dict(dct: dict[str, Any] or list[str, Any], str_to_cvc5_mapping: dict[str, str]) -> str:
    if len(dct) == 0:
        return 'j_nil_dict'
    else:
        if isinstance(dct, dict):
            ldict = list(sorted(dct.items(), key=lambda x: x[0]))
        else:
            ldict = dct

        if ldict[0][0][0] == ldict[0][0][-1] == '"':
            ldict[0][0] = (ldict[0][0][1:-1], ldict[0][1])

        return (f'(dict_cons {ldict[0][0]} {to_cvc5_json_type(ldict[0][1], str_to_cvc5_mapping)} '
                f'{get_cvc5_dict(ldict[1:], str_to_cvc5_mapping)})')


def to_cvc5_json_type(i: Any, str_to_cvc5_mapping: dict[str, str]) -> str:
    if isinstance(i, bool):
        return f'(jB {str(i).lower()})'
    if isinstance(i, str):
        if len(i) > 1 and i[0] == '"' and i[-1] == '"':
            return '(jS ' + str_to_cvc5_mapping[i[1:-1]] + ')'
        return '(jS ' + str_to_cvc5_mapping[i] + ')'
    if isinstance(i, int) or isinstance(i, float):
        return f'(jI {i})'
    if i is None:
        return "jNull"
    if isinstance(i, list):
        return f'(jL {get_cvc5_list(i, str_to_cvc5_mapping)})'
    if isinstance(i, dict):
        return f'(jD {get_cvc5_dict(i, str_to_cvc5_mapping)})'

    raise NotImplementedError(f'to_cvc5 not implemented for {i.__class__.__name__}')


def to_cvc5(i: Any, str_to_cvc5_mapping: dict[str, str]) -> str:
    if isinstance(i, bool):
        return f'{str(i).lower()}'
    if isinstance(i, str):
        if len(i) > 1 and i[0] == '"' and i[-1] == '"':
            return '"' + i[1:-1].replace('"', '\"') + '"'
        return '"' + i.replace('"', '\"') + '"'
    if isinstance(i, int) or isinstance(i, float):
        return f'{i}'
    if i is None:
        return "jNull"
    if isinstance(i, list):
        return f'{get_cvc5_list(i, str_to_cvc5_mapping)}'
    if isinstance(i, dict):
        return f'{get_cvc5_dict(i, str_to_cvc5_mapping)}'

    raise NotImplementedError(f'to_cvc5 not implemented for {i.__class__.__name__}')


def cvc5_file_preamble(cvc5_strs: list[str]) -> str:
    logic_and_options = """
(set-logic UFDTLIA)
(set-option :produce-models true)


; (set-option :sygus-enum smart)
; (set-option :sygus-eval-unfold single)
; (set-option :sygus-grammar-cons simple)
; (set-option :sygus-pbe true)
    """

    rest = """
; recursive datatypes declared together
(declare-datatypes ((Json 0) (JsonDict 0) (JsonList 0)) ((
    (jS (sval EnumString))
    (jI (ival Int))
    (jB (bval Bool))
    (jL (lval JsonList))
    (jD (dval JsonDict))
    (jNull)
  )(
    (j_nil_dict)
    (dict_cons (key EnumString) (val Json) (jdtail JsonDict))
  )(
    (j_nil_list)
    (list_cons   (j_head Json) (j_tail JsonList))
  )
  ))


(define-fun-rec find_key ((keyV EnumString) (dict JsonDict)) Json
  (match dict
  (
    (j_nil_dict jNull)
    ((dict_cons _key _val rest) (ite (= _key keyV) _val (find_key keyV rest)))
  ))
)

(define-fun get_val_dict ((x Json) (keyV EnumString)) Json
  (match x
    (
      ((jS x) jNull)
      ((jI x) jNull)
      ((jB x) jNull)
      ((jL x) jNull)
      ((jD dict) (find_key keyV dict))
      (jNull jNull)
    ))
)

(define-fun-rec nth_list ((li JsonList) (n Int)) Json
  (ite (< n 0)
    jNull
      (match li ((j_nil_list jNull) ((list_cons h r) (ite (= n 0) h (nth_list r (- n 1))))))
  )
)

(define-fun-rec list_length ((li JsonList)) Int
  (match li (
        (j_nil_list 0)
        ((list_cons h t) (+ 1 (list_length t)))
  ))
)

(define-fun-rec dict_length ((dict JsonDict)) Int
  (match dict (
        (j_nil_dict 0)
        ((dict_cons k v t) (+ 1 (dict_length t)))
  ))
)

(define-fun length ((jx Json)) Int
  (match jx (
      ((jS x) 1)
      ((jI x) 1)
      ((jB x) 1)
      ((jL li) (list_length li))
      ((jD dict) (dict_length dict))
      (jNull 0)
    ))
)

(define-fun is_empty ((jx Json)) Bool
  (match jx
    (
      ((jS x) true)
      ((jI x) true)
      ((jB x) true)
      ((jL li) (= li j_nil_list))
      ((jD dict) (= dict j_nil_dict))
      (jNull false)
    ))
)

(define-fun-rec concat_list ((l JsonList) (r JsonList)) JsonList
  (match l
  (
    (j_nil_list r)
    ((list_cons h t) (list_cons h (concat_list t r)))
  ))
)

(define-fun get_idx_list ((x Json) (idx Int)) Json
  (match x
    (
      ((jS x) jNull)
      ((jI x) jNull)
      ((jB x) jNull)
      ((jL li) (nth_list li idx))
      ((jD dict) jNull)
      (jNull jNull)
    ))
)

(define-funs-rec (
  (get_descendants_named ((x Json) (keyV EnumString)) Json)
  (collect_descendants_dict ((xd JsonDict) (keyV EnumString) (accum JsonList)) JsonList)
  )
  ((match x
    (
      (jNull jNull)
      ((jS x) jNull)
      ((jI x) jNull)
      ((jB x) jNull)
      ((jL li) jNull)
      ((jD dict) (let
        ((res (find_key keyV dict)))
        (ite (= res jNull)
          (jL (collect_descendants_dict dict keyV j_nil_list))
          res
        )
      ))))
    (match xd
      ((j_nil_dict accum)
      ((dict_cons _key _val rest)
        (let ((res (get_descendants_named _val keyV)))
          (match res
            (
              (jNull (collect_descendants_dict rest keyV accum))
              ((jS s) (collect_descendants_dict rest keyV (list_cons (jS s) accum)))
              ((jI e) (collect_descendants_dict rest keyV (list_cons (jI e) accum)))
              ((jB e) (collect_descendants_dict rest keyV (list_cons (jB e) accum)))
              ((jD e) (collect_descendants_dict rest keyV (list_cons (jD e) accum)))
              ((jL l) (collect_descendants_dict rest keyV (concat_list l accum)))
            )
          )
        )
      ))
    )
  )
)
"""
    if len(cvc5_strs) == 0:
        string_datatype = """
(declare-datatype EnumString
    ( nilstr )
)
"""
    else:
        string_datatype = f"""
(declare-datatype EnumString
    ( {' '.join('(' + s + ')' for s in cvc5_strs)} )
)
"""

    return logic_and_options + string_datatype + rest


def build_sygus_grammar(keys: list[str], indices: list[int], values: list[int | str],
                        start_symb: str, synt_f_name: str,
                        str_to_cvc5_mapping: dict[str, str]) -> str:
    keys_str = ' '.join(f'{str_to_cvc5_mapping[k]}' for k in keys)
    values_str = ' '.join(to_cvc5_json_type(v, str_to_cvc5_mapping) for v in values)
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
        non_terminals['(SySK EnumString)'] = f'\n    (SySK EnumString ({keys_str}))'

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


def build_cvc5_samples(synt_decl, str_to_cvc5_mapping: dict[str, str]):
    s = ''
    for io_idx, io in enumerate(synt_decl['constraints']):
        s += f'(define-const sample{io_idx} Json {to_cvc5_json_type(io["inputs"], str_to_cvc5_mapping)})\n'
    s += '\n'
    return s


def build_cvc5_synthesis_query(synt_decl, start_symbol, str_to_cvc5_mapping: dict[str, str]):
    asserts = []
    f_name = synt_decl["name"]
    for ctr_idx, ctr in enumerate(synt_decl["constraints"]):
        if start_symbol == 'SyntJ':
            output_str = to_cvc5_json_type(ctr["output"], str_to_cvc5_mapping)
        else:
            output_str = to_cvc5(ctr["output"], str_to_cvc5_mapping)
        asserts.append(f'(constraint (= ({f_name} sample{ctr_idx}) {output_str}))')

    asserts_str = '\n'.join(asserts)

    s = asserts_str
    s += '\n\n(check-synth)\n'
    return s


def to_python(arg):
    try:
        return eval(arg)
    except (NameError, SyntaxError):
        try:
            return eval(arg.replace('true', 'True').replace('false', 'False'))
        except (NameError, SyntaxError):
            return arg


def parse_cvc5_output_aux(tokens: deque):
    two_arg_functions = ['get_idx_list', '=', 'get_descendants_named', 'get_val_dict']
    one_arg_functions = ['not', 'empty', 'jI', 'jS', 'is_empty']
    token = tokens.popleft()
    if token[0] == '(':
        func_name = token[1:]
        if func_name in one_arg_functions:
            arg0 = parse_cvc5_output_aux(tokens)
            return func_name, arg0
        elif func_name in two_arg_functions:
            arg0 = parse_cvc5_output_aux(tokens)
            arg1 = parse_cvc5_output_aux(tokens)
            return func_name, (arg0, arg1)
        if func_name == 'choose':
            # ignore
            return parse_cvc5_output_aux(tokens)
    if 'x' in token:
        return 'x'
    if token[-1] == ')':
        token = token.replace(')', '')
        try:
            return eval(token)
        except NameError:
            return token  # Assume it is a string

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
    _ = tokens.popleft()  # func name
    _ = tokens.popleft()  # x
    _ = tokens.popleft()  # x type, Json
    _ = tokens.popleft()  # return type, start symb

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


def get_cvc5_enum_type_str(s: str) -> str:
    if len(s) == 0:
        return 'emptystr'
    if s[0].isdigit():
        s = '_' + s

    # Replace invalid characted in CVC5 identifiers with valid characters.
    replacements = {' ': '-', ':': '_', '(': '<', ')': '>'}
    for k, v in replacements.items():
        s = s.replace(k, v)
    return s


def get_cvc5_enum_type_strs(strs: list[str]) -> dict[str, str]:
    str_to_cvc5_mappting = {}
    cvc5_to_str_mapping = {}
    for s in strs:
        cvc5_str = get_cvc5_enum_type_str(s)
        while cvc5_str in cvc5_to_str_mapping and cvc5_to_str_mapping[cvc5_str] != s:
            cvc5_str = f'_{cvc5_str}'
        assert (s not in str_to_cvc5_mappting or
                str_to_cvc5_mappting[s] == cvc5_str), \
            (f'Tried to map {s} to {cvc5_str} but it was '
             f'already mapped to {str_to_cvc5_mappting[s]}')
        str_to_cvc5_mappting[s] = cvc5_str
        cvc5_to_str_mapping[cvc5_str] = s

    return str_to_cvc5_mappting


# FIXME on main: Weird arg order
def get_cvc5_query(indices, keys, synt_decl, values):
    cvc5_text = ''
    str_to_cvc5_mapping = get_cvc5_enum_type_strs(sorted(get_synthesis_strings(synt_decl)))
    assert all(k in str_to_cvc5_mapping for k in keys), tuple(filter(lambda k: k not in str_to_cvc5_mapping, keys))
    assert all(not isinstance(v, str) or v in str_to_cvc5_mapping for v in values), (
        tuple(filter(lambda v: isinstance(v, str) and v not in str_to_cvc5_mapping, values)))
    cvc5_text += cvc5_file_preamble(sorted(str_to_cvc5_mapping.values()))
    start_symbol = get_start_symbol(synt_decl['constraints'])
    start_symbol = start_symbol[0].upper() + start_symbol[1:]
    f_name = synt_decl["name"]
    cvc5_text += build_sygus_grammar(keys, indices, values, start_symbol, f_name, str_to_cvc5_mapping)
    cvc5_text += build_cvc5_samples(synt_decl, str_to_cvc5_mapping)
    cvc5_text += build_cvc5_synthesis_query(synt_decl, start_symbol, str_to_cvc5_mapping)
    return cvc5_text


def run_cvc5_command(cvc5_filename: str, timeout: int) -> str:
    """
    Runs a pre-written CVC5 Sygus file and returns the solution, in our jsonpath format.
    :param cvc5_filename: The name of the file with the sygus problem
    :param timeout: Synthesis timeout in seconds
    :return: solution in jsonpath format
    """
    cvc5_command = get_timeout_command_prefix(timeout) + ['cvc5', cvc5_filename]
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
                    f'Something wrong with CVC5 output to '
                    f'{" ".join(cvc5_command)}:\n'
                    f'stdout: {result.stdout}\n{e}')
        if len(result.stderr) > 0:
            print('CVC5 call stderr:', result.stderr)
        return cvc5_out

    except subprocess.TimeoutExpired:
        return f'(timeout {human_time(timeout)})'
