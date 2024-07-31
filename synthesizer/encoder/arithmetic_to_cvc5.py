import re
import subprocess
from collections import deque
from typing import Any

from synthesizer.util import get_timeout_command_prefix, human_time, SyntDecl


def get_arithmetic_start_symbol(ctrs: list[dict[str, Any]], in_type: str) -> str:
    """ Returns the start symbol for the arithmetic grammar, depending on the type of the outputs. """
    if all(isinstance(ctr['output'], bool) for ctr in ctrs):
        start_symb = 'SyntBool'
    elif all(isinstance(ctr['output'], int) for ctr in ctrs) and in_type == 'Real':
        # If the output is an int, but the input is real, we need to use the real start symbol
        start_symb = 'SyntReal'
    elif all((isinstance(ctr['output'], int) and not isinstance(ctr['output'], bool))
             or isinstance(ctr['output'], float)
             for ctr in ctrs) and in_type == 'Real':
        # If some outputs are ints, but at least one is real, we need to use the real start symbol
        start_symb = 'SyntReal'
    elif all(isinstance(ctr['output'], int) for ctr in ctrs):
        start_symb = 'SyntInt'
    elif all(isinstance(ctr['output'], float) for ctr in ctrs):
        start_symb = 'SyntReal'
    else:
        raise NotImplementedError(f'Which start symbol for '
                                  f'{[ctr["output"].__class__.__name__ for ctr in ctrs]}')
    return start_symb


def get_arithmetic_input_type(ctrs: list[dict[str, Any]]) -> str:
    """ Returns the input type for the arithmetic grammar, depending on the type of the inputs. """
    if all(any(isinstance(i, float) for i in ctr["inputs"]) for ctr in ctrs):
        in_type = 'Real'
    elif all(all(isinstance(i, int) for i in ctr["inputs"]) for ctr in ctrs):
        in_type = 'Int'
    else:
        raise NotImplementedError(f'Which input type for '
                                  f'{[ctr["output"].__class__.__name__ for ctr in ctrs]}')
    return in_type


class Arithmetic2CVC5Encoder:
    """ Encodes arithmetic synthesis problems into CVC5 (SMTLib) SyGuS format. """

    def get_cvc5_list(self, lst: list[Any]):
        """ Returns a string representation of a list for CVC5. """
        if len(lst) == 0:
            return 'il_nil'
        else:
            return f'(il_cons {self.to_cvc5(lst[0])} {self.get_cvc5_list(lst[1:])})'

    def to_cvc5(self, i: Any) -> str:
        """ Returns a representation of an object for CVC5. """
        if isinstance(i, bool):
            return f'{str(i).lower()}'
        if isinstance(i, str):
            if len(i) > 1 and i[0] == '"' and i[-1] == '"':
                return '"' + i[1:-1].replace('"', '\"') + '"'
            return '"' + i.replace('"', '\"') + '"'
        if isinstance(i, int) or isinstance(i, float):
            if i >= 0:
                return f'{i}'
            else:
                return f'(- {abs(i)})'
        if isinstance(i, list):
            return f'{self.get_cvc5_list(i)}'

        raise NotImplementedError(f'to_cvc5 not implemented for {i.__class__.__name__}')

    def _cvc5_file_preamble(self, in_type: str):
        """ Returns the preamble for a CVC5 file, with all necessary functions and types definitions. """
        return f"""(set-logic ALL)
(set-option :produce-models true)

; (set-option :sygus-enum smart)
(set-option :sygus-eval-unfold single)
(set-option :sygus-grammar-cons simple)
(set-option :sygus-pbe true)

(declare-datatype NumList (
    (il_nil)
    (il_cons (il_head {in_type}) (il_tail NumList))
  ))
  
(declare-datatype Null ( (Null) ))

(define-fun-rec nth_list ((li NumList) (n Int)) {in_type}
  (ite (< n 0)
    {'0' if in_type == 'Int' else '0.0'}
    (match li (
      (il_nil {'0' if in_type == 'Int' else '0.0'}) 
      ((il_cons h r) (ite (= n 0) 
        h 
        (nth_list r (- n 1)))
      ))
    )
  )
)

(define-fun-rec list_length ((li NumList)) Int
  (match li (
        (il_nil 0)
        ((il_cons h t) (+ 1 (list_length t)))
  ))
)

(define-fun-rec powi ((x Int) (y Int)) Int
  (ite (< y 0) 
    0 
    (ite 
      (= y 0) 
      1 
      (* x (powi x (- y 1)))
    )
  )
)

(define-fun-rec powr ((x Real) (y Int)) Real
  (ite (< y 0) 
    0.0
    (ite 
      (= y 0) 
      1.0 
      (* x (powr x (- y 1)))
    )
  )
)

(define-fun is_empty ((l NumList)) Bool
  (= l il_nil)
)

(define-fun-rec concat_list ((l NumList) (r NumList)) NumList
  (match l
  (
    (il_nil r)
    ((il_cons h t) (il_cons h (concat_list t r)))
  ))
)
"""

    def build_sygus_grammar(self, start_symb: str, in_type: str, synt_f_name: str = 'f0'):
        """ Returns the SyGuS grammar for the an arithmetic synthesis problem. """
        if start_symb == 'SyntInt':
            start_type = 'Int'
        elif start_symb == 'SyntBool':
            start_type = 'Bool'
        elif start_symb == 'SyntReal':
            start_type = 'Real'
        else:
            raise NotImplementedError(f'Unknown type for start symbol {start_symb}')

        non_terminals = {}
        synth_bool_definition = """
    (SyntBool Bool (
      (is_empty SyntList)
      (not SyntBool)
      (< SyntInt SyntInt)
      (< SyntInt SyntReal)
      (< SyntReal SyntReal)
      (< SyntReal SyntInt)
      (> SyntInt SyntInt)
      (> SyntInt SyntReal)
      (> SyntReal SyntReal)
      (> SyntReal SyntInt)
      (<= SyntInt SyntInt)
      (<= SyntInt SyntReal)
      (<= SyntReal SyntReal)
      (<= SyntReal SyntInt)
      (>= SyntInt SyntInt)
      (>= SyntInt SyntReal)
      (>= SyntReal SyntReal)
      (>= SyntReal SyntInt)
      (= SyntInt SyntInt)
      (= SyntReal SyntReal)"""
        synth_bool_definition += '\n    ))'
        non_terminals['(SyntBool Bool)'] = synth_bool_definition

        if in_type == 'Int':
            synth_int_definition = f"""
    (SyntInt Int (
      (nth_list SyntList SyntInt)
      (+ SyntInt SyntInt)
      (- SyntInt SyntInt)
      (* SyntInt SyntInt)
      (powi SyntInt SyntInt)
      (abs SyntInt)
      (Constant Int) """
            synth_int_definition += '\n    ))'
            non_terminals['(SyntInt Int)'] = synth_int_definition

        elif in_type == 'Real':
            synth_real_definition = f"""
    (SyntReal Real (
      (+ SyntReal SyntReal)
      (- SyntReal SyntReal)
      (* SyntReal SyntReal)
      (* SyntInt SyntReal)
      (/ SyntReal SyntReal)
      (/ SyntInt SyntReal)
      (/ SyntReal SyntInt)
      (/ SyntInt SyntInt)
      (powr SyntReal SyntInt)
      (abs SyntReal)
      (nth_list SyntList SyntInt)"""
            synth_real_definition += '\n    ))'
            non_terminals['(SyntReal Real)'] = synth_real_definition

            synth_int_definition = f"""
    (SyntInt Int (
      (+ SyntInt SyntInt)
      (- SyntInt SyntInt)
      (* SyntInt SyntInt)
      (powi SyntInt SyntInt)
      (abs SyntInt)
      (Constant Int)"""
            synth_int_definition += '\n    ))'
            non_terminals['(SyntInt Int)'] = synth_int_definition
        else:
            raise NotImplementedError(f'Unknown type for start symbol {start_symb}')

        synth_numlist_definition = """
    (SyntList NumList (
      x"""
        synth_numlist_definition += '\n    ))'
        non_terminals['(SyntList NumList)'] = synth_numlist_definition

        non_terminals_list = list(sorted(non_terminals.items()))
        start_symbol_pair_t = tuple(filter(lambda p: start_symb in p[0], non_terminals_list))
        assert len(start_symbol_pair_t) == 1, (
            f'Expected to find exactly one start symbol, but found {start_symbol_pair_t}.\n '
            f'Looking for {start_symb} in {non_terminals.keys()}')
        start_symbol_pair = start_symbol_pair_t[0]
        non_terminals_list.remove(start_symbol_pair)
        non_terminals_list.insert(0, start_symbol_pair)
        s = f"""
(synth-fun {synt_f_name} ((x NumList)) {start_type}
  ;;Non terminals of the grammar
  ( """
        s += ' '.join(map(lambda p: p[0], non_terminals_list))
        s += """ )
  ;;Define the grammar
  ("""
        s += '\n  '.join(map(lambda p: p[1], non_terminals_list))
        s += '\n  )\n)\n'
        return s

    def build_cvc5_samples(self, synt_decl: SyntDecl, in_type: str):
        """ Returns the samples for the CVC5 synthesis problem. """
        s = ''
        for io_idx, io in enumerate(synt_decl['constraints']):
            if in_type == 'Int':
                s_inputs = self.to_cvc5([int(i) for i in io["inputs"]])
            elif in_type == 'Real':
                s_inputs = self.to_cvc5([float(i) for i in io["inputs"]])
            else:
                raise NotImplementedError(f'Unknown type for start symbol {in_type}')
            s += f'(define-const sample{io_idx} NumList {s_inputs})\n'
        s += '\n'
        return s

    def build_cvc5_synthesis_query(self, synt_decl: SyntDecl, in_type: str):
        """ Returns the synthesis query for the CVC5 synthesis problem. """
        asserts = []
        f_name = synt_decl['name']
        for ctr_idx, ctr in enumerate(synt_decl['constraints']):
            if (in_type == 'Real' and not isinstance(ctr['output'], bool) and
                    isinstance(ctr['output'], int)):
                # If the output is int (not Bool) but inputs were floats, convert output to float
                ctr['output'] = float(ctr['output'])
            output_str = self.to_cvc5(ctr['output'])
            asserts.append(f'(constraint (= ({f_name} sample{ctr_idx}) {output_str}))')

        asserts_str = '\n'.join(asserts)

        s = asserts_str
        s += '\n\n(check-synth)\n'
        return s

    def parse_cvc5_output_aux(self, tokens: deque):
        two_arg_functions = ['get_idx_list', '=', 'nth_list', '+', '*', '-', '/', 'powi', 'powr', '>=', '<=', '>', '<']
        one_arg_functions = ['not', 'empty', 'is_empty', 'abs']
        token = tokens.popleft()
        if token == '(-' and re.fullmatch(r'\d+\)', tokens[0]):
            return -int(tokens.popleft()[:-1])
        if token[0] == '(':
            func_name = token[1:]
            if func_name in one_arg_functions:
                arg0 = self.parse_cvc5_output_aux(tokens)
                return (func_name, (arg0))
            elif func_name in two_arg_functions:
                arg0 = self.parse_cvc5_output_aux(tokens)
                arg1 = self.parse_cvc5_output_aux(tokens)
                return (func_name, (arg0, arg1))
            if func_name == 'choose':
                # ignore
                return self.parse_cvc5_output_aux(tokens)
        if 'x' in token:
            return 'x'
        if token[-1] == ')':
            return eval(token.replace(')', ''))
        try:
            return int(token)
        except ValueError:
            try:
                return float(token)
            except ValueError:
                pass

        raise NotImplementedError(f'Handle parsing "{token}", {tokens}')

    def parse_cvc5_output(self, solver_output: str):
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

        return self.parse_cvc5_output_aux(tokens)

    def cvc5_to_jsonpath(self, ast):
        input_name = 'x'
        if isinstance(ast, tuple):
            f_name, f_args = ast

            if f_name == 'nth_list':
                a0, a1 = f_args
                return f'{self.cvc5_to_jsonpath(a0)}[{a1}]'
            elif f_name == '=':
                a0, a1 = f_args
                return f'({self.cvc5_to_jsonpath(a0)} == {self.cvc5_to_jsonpath(a1)})'
            elif f_name == 'not':
                a0 = f_args
                return f'! ({self.cvc5_to_jsonpath(a0)})'
            elif f_name == 'abs':
                a0 = f_args
                return f'|{self.cvc5_to_jsonpath(a0)}|'
            elif f_name == 'is_empty':
                a0 = f_args
                return f'(len({self.cvc5_to_jsonpath(a0)}) == 0)'
            elif f_name == 'jI' or f_name == 'jS':
                a0 = f_args
                return f'{self.cvc5_to_jsonpath(a0)}'
            elif f_name == 'powi' or f_name == 'powr':
                a0, a1 = f_args
                return f'({self.cvc5_to_jsonpath(a0)} ** {self.cvc5_to_jsonpath(a1)})'
            elif f_name in ('+', '-', '*', '/', '==', '>=', '<=', '>', '<'):
                a0, a1 = f_args
                return f'({self.cvc5_to_jsonpath(a0)} {f_name} {self.cvc5_to_jsonpath(a1)})'
            else:
                raise NotImplementedError(f'cvc5_to_jsonpath not implemented for operation {f_name}.')
        elif ast == input_name:
            return '$'
        if isinstance(ast, str):
            return f'"{ast}"'
        else:
            return ast

    def convert_cvc5_to_jsonpath(self, solver_output: str):
        ast = self.parse_cvc5_output(solver_output)
        return self.cvc5_to_jsonpath(ast)

    def get_query(self, synt_decl):
        """ Returns the CVC5 query for a given arithmetic synthesis problem. """
        in_type = get_arithmetic_input_type(synt_decl['constraints'])
        start_symbol = get_arithmetic_start_symbol(synt_decl['constraints'], in_type)
        start_symbol = start_symbol[0].upper() + start_symbol[1:]
        f_name = synt_decl["name"]

        cvc5_text = ''
        cvc5_text += self._cvc5_file_preamble(in_type)
        cvc5_text += self.build_sygus_grammar(start_symbol, in_type, f_name)
        cvc5_text += self.build_cvc5_samples(synt_decl, in_type)
        cvc5_text += self.build_cvc5_synthesis_query(synt_decl, in_type)
        return cvc5_text

    def run_command(self, cvc5_filename: str, timeout: int) -> str:
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
                # subprocess.run(['subl', cvc5_filename])
                raise RuntimeError(f'Error in CVC5 '
                                   f'{" ".join(cvc5_command)}:\n'
                                   f'stdout: {result.stdout}\n'
                                   f'stderr: {result.stderr}')
            else:
                cvc5_out = "\n".join(result.stdout.split('\n'))
                try:
                    cvc5_out = self.convert_cvc5_to_jsonpath(cvc5_out)
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
