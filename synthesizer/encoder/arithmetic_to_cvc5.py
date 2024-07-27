import subprocess
from collections import deque
from typing import Any

from synthesizer.util import get_timeout_command_prefix, human_time


def get_start_symbol(ctrs: list[dict[str, Any]]) -> str:
    if all(isinstance(ctr["output"], bool) for ctr in ctrs):
        start_symb = 'SyntBool'
    elif all(isinstance(ctr["output"], int) for ctr in ctrs):
        start_symb = 'SyntInt'
    elif all(isinstance(ctr["output"], float) for ctr in ctrs):
        start_symb = 'SyntReal'
    else:
        raise NotImplementedError(f'Which start symbol for '
                                  f'{[ctr["output"].__class__.__name__ for ctr in ctrs]}')
    return start_symb


class Arithmetic2CVC5Encoder:
    def get_cvc5_list(self, lst: list[Any]):
        if len(lst) == 0:
            return 'il_nil'
        else:
            return f'(il_cons {self.to_cvc5(lst[0])} {self.get_cvc5_list(lst[1:])})'

    def to_cvc5(self, i: Any) -> str:
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

    def _cvc5_file_preamble(self):
        return """
    (set-logic ALL)
    (set-option :produce-models true)
    
    ; (set-option :sygus-enum smart)
    (set-option :sygus-eval-unfold single)
    (set-option :sygus-grammar-cons simple)
    (set-option :sygus-pbe true)
    
    (declare-datatype IntList (
        (il_nil)
        (il_cons (il_head Int) (il_tail IntList))
      ))
      
    (declare-datatype Null ( (Null) ))
    
    (define-fun-rec nth_list ((li IntList) (n Int)) Int
      (ite (< n 0)
        0
        (match li ((il_nil 0) ((il_cons h r) (ite (= n 0) h (nth_list r (- n 1))))))
      )
    )
    
    (define-fun-rec list_length ((li IntList)) Int
      (match li (
            (il_nil 0)
            ((il_cons h t) (+ 1 (list_length t)))
      ))
    )
    
    (define-fun is_empty ((l IntList)) Bool
      (= l il_nil)
    )
    
    (define-fun-rec concat_list ((l IntList) (r IntList)) IntList
      (match l
      (
        (il_nil r)
        ((il_cons h t) (il_cons h (concat_list t r)))
      ))
    )
    """

    def build_sygus_grammar(self, indices, start_symb: str, synt_f_name: str = 'f0'):
        if start_symb == 'SyntInt':
            start_type = 'Int'
        elif start_symb == 'SyntBool':
            start_type = 'Bool'
        elif start_symb == 'SyntReal':
            start_type = 'Real'
        else:
            raise NotImplementedError(f'Unknown type for start symbol {start_symb}')
        non_terminals = {}
        indices_str = ' '.join(map(str, indices))
        synth_bool_definition = """
        (SyntBool Bool (
          (is_empty SyntList)
          (not SyntBool)"""
        synth_bool_definition += '\n    ))'
        non_terminals['(SyntBool Bool)'] = synth_bool_definition

        synth_int_definition = f"""
                (SyntInt Int (
                  (+ SyntInt SyntInt)
                  (* SyntInt SyntInt)
                  (abs SyntInt)
                  (nth_list SyntList SyntInt)
                  {indices_str} """
        synth_int_definition += '\n    ))'
        non_terminals['(SyntInt Int)'] = synth_int_definition

        synth_list_definition = """
                        (SyntList IntList (
                          x
                          """
        synth_list_definition += '\n    ))'
        non_terminals['(SyntList IntList)'] = synth_list_definition

        non_terminals_list = list(sorted(non_terminals.items()))
        start_symbol_pair = tuple(filter(lambda p: start_symb in p[0], non_terminals_list))
        assert len(start_symbol_pair) == 1, (
            f'Expected to find exactly one start symbol, but found {start_symbol_pair}.\n '
            f'Looking for {start_symb} in {non_terminals.keys()}')
        start_symbol_pair = start_symbol_pair[0]
        non_terminals_list.remove(start_symbol_pair)
        non_terminals_list.insert(0, start_symbol_pair)

        s = f"""
    (synth-fun {synt_f_name} ((x IntList)) {start_type}
      ;;Non terminals of the grammar
      ( """
        s += ' '.join(map(lambda p: p[0], non_terminals_list))
        s += """ )
      ;;Define the grammar
      ("""
        s += '\n  '.join(map(lambda p: p[1], non_terminals_list))
        s += '\n  )\n)\n'
        return s

    def build_cvc5_samples(self, synt_decl):
        s = ''
        for io_idx, io in enumerate(synt_decl['constraints']):
            s += f'(define-const sample{io_idx} IntList {self.to_cvc5(io["inputs"])})\n'
        s += '\n'
        return s

    def build_cvc5_synthesis_query(self, synt_decl, start_symbol):
        asserts = []
        f_name = synt_decl['name']
        for ctr_idx, ctr in enumerate(synt_decl['constraints']):
            if start_symbol == 'SyntJ':
                output_str = self.to_cvc5_json_type(ctr['output'])
            else:
                output_str = self.to_cvc5(ctr['output'])
            asserts.append(f'(constraint (= ({f_name} sample{ctr_idx}) {output_str}))')

        asserts_str = '\n'.join(asserts)

        s = asserts_str
        s += '\n\n(check-synth)\n'
        return s

    def to_python(self, arg):
        try:
            return eval(arg)
        except (NameError, SyntaxError) as e:
            try:
                return eval(arg.replace('true', 'True').replace('false', 'False'))
            except (NameError, SyntaxError) as e:
                return arg

    def parse_cvc5_output_aux(self, tokens: deque):
        two_arg_functions = ['get_idx_list', '=', 'nth_list']
        one_arg_functions = ['not', 'empty', 'is_empty', 'abs']
        token = tokens.popleft()
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

        raise NotImplementedError(f'Handle parsing {token}, {tokens}')

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

            if f_name == 'get_val_dict':
                a0, a1 = f_args
                return f'{self.cvc5_to_jsonpath(a0)}.{a1}'
            elif f_name == 'get_descendants_named':
                a0, a1 = f_args
                return f'{self.cvc5_to_jsonpath(a0)}..{a1}'
            elif f_name == 'nth_list':
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
            else:
                raise NotImplementedError(f'to_jsonpath not implemented for operation {f_name}.')
        elif ast == input_name:
            return '$'
        if isinstance(ast, str):
            return f'"{ast}"'
        else:
            return ast

    def convert_cvc5_to_jsonpath(self, solver_output: str):
        ast = self.parse_cvc5_output(solver_output)
        return self.cvc5_to_jsonpath(ast)

    def get_query(self, synt_decl, indices):
        cvc5_text = ''
        cvc5_text += self._cvc5_file_preamble()
        start_symbol = get_start_symbol(synt_decl['constraints'])
        start_symbol = start_symbol[0].upper() + start_symbol[1:]
        f_name = synt_decl["name"]
        cvc5_text += self.build_sygus_grammar(indices, start_symbol, f_name)
        cvc5_text += self.build_cvc5_samples(synt_decl)
        cvc5_text += self.build_cvc5_synthesis_query(synt_decl, start_symbol)
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
                subprocess.run(['subl', cvc5_filename])
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
