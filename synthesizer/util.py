import datetime
import enum
import hashlib
import os
import signal
import sys
from collections import deque
from typing import Any

Solution = dict[str, int | str]
SyntDecl = dict[str:Any]

# Active children are the PID of children processes currently running
active_children: set[int] = set()


def handler(signum, frame):
    for pid in active_children:
        print(f"Killing subprocess {pid}")
        os.kill(pid, signal.SIGINT)
        os.kill(pid, signal.SIGKILL)
    sys.exit(128 + signum)


def human_time(total_seconds: int | float) -> str:
    """ Prints a time in a nice, legible format. """
    if total_seconds < .1:
        return f'< 0.1s'
    elif total_seconds < 60:
        return f'{total_seconds:.1f}s'
    mins, secs = divmod(total_seconds, 60)
    hours, mins = divmod(mins, 60)
    days, hours = divmod(hours, 24)
    ret = ''
    if days > 0:
        ret += f'{round(days)}d'
    if hours > 0:
        ret += f'{round(hours)}h'
    if mins > 0:
        ret += f'{round(mins)}m'
    ret += f'{round(secs)}s'
    return ret


SynthesisSolver = enum.Enum('SynthesisSolver', ['CVC5', 'Rosette'])


def get_timestamp() -> str:
    """
    Get a timestamp in the format YYYYMMDDHHMMSS
    :return: timestamp string
    """
    now = datetime.datetime.now()
    timestamp = now.strftime("%Y%m%d%H%M%S")
    return timestamp


def my_hash(s: str) -> int:
    return abs(int(hashlib.sha512(s.encode('utf-8')).hexdigest(), 16) % 10 ** 12)


def get_synthesis_filename(depth: int, func_name: str, instance_name: str, keys: list[str],
                           values: list[str], extenstion: str = 'txt') -> str:
    timestamp = get_timestamp()

    return (f'{instance_name}{"" if func_name[0] == "_" else "_"}'
            f'{func_name}'
            # f'_{my_hash(str(keys) + str(values))}'
            f'_{str(depth) + "_" if depth is not None else ""}'
            f'{timestamp}.{extenstion}')


def get_timeout_command_prefix(timeout: int) -> list[str]:
    return ['timeout', '-k', str(timeout + 2), str(timeout + 1)]


def get_index_of_closing_bracket(str, opening_idx):
    # If input is invalid.
    if str[opening_idx] != '(':
        return -1

    d = deque()  # stack
    for k in range(opening_idx, len(str)):
        if str[k] == ')':
            d.popleft()  # Pop an opening bracket for every closing bracket
        elif str[k] == '(':
            d.append(str[opening_idx])  # Push starting brackets
        if not d:  # If deque becomes empty
            return k

    return -1


def remove_let_expressions_smt2(smt2_solution):
    while '(let' in smt2_solution:
        let_idx = smt2_solution.index('(let')
        closing_bracket = get_index_of_closing_bracket(smt2_solution, let_idx)
        let_expression_complete = smt2_solution[let_idx:closing_bracket + 1]
        # let expression is of the form (let ((var1 val1) (var2 val2) ...) body)
        # the goal is to replace the let expression with body, where all
        # occurrences of var1, var2, ... are replaced by val1, val2, ....
        let_expression = let_expression_complete[1:-1]  # remove the outer brackets
        opening_bracket = let_expression.index('(')
        closing_bracket = get_index_of_closing_bracket(let_expression, 4)
        bindings_str = let_expression[opening_bracket + 1:closing_bracket]
        body = let_expression[closing_bracket + 1:]
        bindings = []
        while len(bindings_str) > 0:
            assert bindings_str[0] == '('
            closing_bracket = get_index_of_closing_bracket(bindings_str, 0)
            binding = bindings_str[1:closing_bracket]
            bindings_str = bindings_str[closing_bracket + 1:]
            var, val = binding.split(' ', 1)
            bindings.append((var, val))

        for var, val in bindings:
            body = body.replace(var, val)
        assert let_expression_complete in smt2_solution
        smt2_solution = smt2_solution.replace(let_expression_complete, body)
        for var, val in bindings:
            assert var not in smt2_solution
    return smt2_solution
