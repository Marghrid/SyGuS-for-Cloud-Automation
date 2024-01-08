import os
from collections import deque
from typing import Any

from synthesizer.to_synthesis import get_start_symbol


def get_cvc5_list(lst: list[Any]):
    if len(lst) == 0:
        return 'j_nil_list'
    else:
        return f'(list_cons {to_cvc5(lst[0])} {get_cvc5_list(lst[1:])})'


def get_cvc5_dict(dct: dict[str, Any] or list[str, Any]):
    if len(dct) == 0:
        return 'j_nil_dict'
    else:
        if isinstance(dct, dict):
            ldict = list(sorted(dct.items(), key=lambda x: x[0]))
        else:
            ldict = dct
        return (f'(dict_cons {to_cvc5(ldict[0][0])} {to_cvc5(ldict[0][1])} '
                f'{get_cvc5_dict(ldict[1:])})')


def to_cvc5(i: Any):
    if isinstance(i, bool):
        return str(i).lower()
    if isinstance(i, str):
        return '(jS "' + i.replace('"', '\\"') + '")'
    if isinstance(i, int) or isinstance(i, float):
        return f'(jI {i})'
    if i is None:
        return "jNull"
    if isinstance(i, list):
        return get_cvc5_list(i)
    if isinstance(i, dict):
        return get_cvc5_dict(i)

    raise NotImplementedError(f'to_cvc5 not implemented for {i.__class__.__name__}')


def cvc5_file_preamble():
    with open(f'{os.getcwd()}/resources/synthesis/synthesis_lang.smt') as f:
        return f.read() + '\n\n'


def build_sygus_grammar(keys, indices, values, start_symb: str):
    keys_str = ' '.join(f'"{k}"' for k in keys)
    values_str = ' '.join(f'"{v}"' if isinstance(v, str) else f'{v}' for v in values)
    indices_str = ' '.join(map(str, indices))

    s = f"""
(synth-fun json-selector ((x Json)) Json
  ;;Non terminals of the grammar
  ((SynthJ Json) (SySK String) (SySV String) (SynthInt Int) (SynthBool Bool))
  ;;Define the grammar
  (
    (SynthBool Bool (
      (empty SynthJ)
      (not SynthBool)"""
    if len(values) > 0:
        s += '\n      (= SynthJ (jS SySV))'
    s += '\n    )'
    s += """
  ]
   (SynthJ Json (
      (get_idx_list x SynthInt)
    (length (syntJ))"""
    if len(keys) > 0:
        s += f"""
    (get_val_dict SynthJ SySK)
    (get_descendants_named SynthJ SySK)"""

    s += "\n      (get_idx_list SynthJ SynthInt)"
    if len(values) > 0:
        s += '\n(syntAdd (syntVal) (syntJ))'
    s += "\n   )]"

    if len(keys) > 0:
        s += f'\n    (SySK String ({keys_str}))'

    s += f"\n    (SynthInt Int ({indices_str}))"
    if len(values) > 0:
        s += f'\n    (SySV String (choose {values_str}))'
    s += '\n  )\n\n'
    return s


def build_cvc5_samples(synt_decl):
    s = ''
    for io_idx, io in enumerate(synt_decl['constraints']):
        s += f'(define-const sample{io_idx} Json {to_cvc5(io["inputs"])})\n'
    s += '\n'
    return s


def build_cvc5_synthesis_query(synt_decl, depth):
    asserts = []
    f_name = synt_decl["name"]
    for ctr_idx, ctr in enumerate(synt_decl["constraints"]):
        asserts.append(f'(constraint (= ({f_name} sample{ctr_idx}) {to_cvc5(ctr["output"])}))')

    asserts_str = '\n'.join(asserts)

    s = '\n\n(check-synth)\n'
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
    raise NotImplementedError(f'Handle parsing {tokens}')
    two_arg_functions = ['child', 'index', 'descendant', 'syntEq']
    one_arg_functions = ['not', 'empty?']
    token = tokens.popleft()
    if token[0] == '(':
        func_name = token[1:]
        if func_name in one_arg_functions:
            arg0 = parse_rosette_output_aux(tokens)
            return (func_name, (arg0))
        elif func_name in two_arg_functions:
            arg0 = parse_rosette_output_aux(tokens)
            arg1 = parse_rosette_output_aux(tokens)
            return (func_name, (arg0, arg1))
        if func_name == 'choose':
            # ignore
            return parse_rosette_output_aux(tokens)
    if 'x' in token:
        return 'x'
    if token[-1] == ')':
        return eval(token.replace(')', ''))

    raise NotImplementedError(f'Handle parsing {token}')


def parse_cvc5_output(rosette: str):
    tokens = deque(rosette.split())
    token = tokens.popleft()
    assert token == '(define-fun', f'removed {token} from {tokens}.'
    token = tokens.popleft()  # func name
    token = tokens.popleft()  # x
    token = tokens.popleft()  # x type, Json
    token = tokens.popleft()  # return type, start symb

    return parse_cvc5_output_aux(tokens)


def to_jsonpath(ast):
    input_name = 'x'
    if isinstance(ast, tuple):
        f_name, f_args = ast

        if f_name == 'child':
            a0, a1 = f_args
            return f'{to_jsonpath(a0)}.{a1}'
        elif f_name == 'descendant':
            a0, a1 = f_args
            return f'{to_jsonpath(a0)}..{a1}'
        elif f_name == 'index':
            a0, a1 = f_args
            return f'{to_jsonpath(a0)}[{a1}]'
        elif f_name == 'syntEq':
            a0, a1 = f_args
            return f'({to_jsonpath(a0)} == {to_jsonpath(a1)})'
        elif f_name == 'not':
            a0 = f_args
            return f'! ({to_jsonpath(a0)})'
        elif f_name == 'empty?':
            a0 = f_args
            return f'(len({to_jsonpath(a0)}) == 0)'
        else:
            raise NotImplementedError(f'to_jsonpath not implemented for operation {f_name}.')
    elif ast == input_name:
        return '$'
    if isinstance(ast, str):
        return f'"{ast}"'
    else:
        return ast


def convert_cvc5_to_jsonpath(rosette: str):
    ast = parse_cvc5_output(rosette)
    return to_jsonpath(ast)


def get_cvc5_query(depth, indices, keys, synt_decl, values):
    rosette_text = ''
    rosette_text += cvc5_file_preamble()
    start_symbol = get_start_symbol(synt_decl['constraints'])
    rosette_text += build_sygus_grammar(keys, indices, values, start_symbol)
    rosette_text += build_cvc5_samples(synt_decl)
    rosette_text += build_cvc5_synthesis_query(synt_decl, depth)
    return rosette_text
