from typing import Any

import dateutil.parser


def get_synthesis_keys_aux(i: Any, depth: int = 0, max_depth: int = 100000) -> set[str]:
    if depth >= max_depth:
        return set()
    if i is None:
        return set()
    if isinstance(i, str):
        return set()
    if isinstance(i, int):
        return set()
    if isinstance(i, list):
        return set().union(*(get_synthesis_keys_aux(e, depth + 1, max_depth) for e in i))
    if isinstance(i, dict):
        return set(i.keys()).union(*(get_synthesis_keys_aux(v, depth + 1, max_depth) for v in i.values()))

    raise NotImplementedError(f'get_racket_keys_aux not implemented for {i.__class__.__name__}')


def get_synthesis_values_aux(i: Any) -> set[Any]:
    if i is None:
        return set()
    if isinstance(i, bool):
        return set()
    if isinstance(i, str):
        try:
            dateutil.parser.parse(i)
            return set()
        except (dateutil.parser._parser.ParserError, OverflowError):
            return {i.replace('"', '\\"')}
    if isinstance(i, int):
        return {i}
    if isinstance(i, list):
        return set().union(*(get_synthesis_values_aux(e) for e in i))
    if isinstance(i, dict):
        return set().union(*(get_synthesis_values_aux(v) for v in i.values()))

    raise NotImplementedError(f'get_racket_values_aux not implemented '
                              f'for {i.__class__.__name__}')


def get_synthesis_max_list_index(i: Any) -> int:
    if isinstance(i, str):
        return 0
    if isinstance(i, int):
        return 0
    if i is None:
        return 0
    if isinstance(i, list):
        if len(i) == 0:
            return 0
        return max([len(i)] + [get_synthesis_max_list_index(e) for e in i])
    if isinstance(i, dict):
        if len(i) == 0:
            return 0
        return max([get_synthesis_max_list_index(e) for e in i.values()])

    raise NotImplementedError(f'get_racket_max_list_index not implemented '
                              f'for {i.__class__.__name__}')


def get_synthesis_keys(synt_decl: dict[str:Any],
                       max_depth: int = 100000) -> set[str]:
    """ Given the contraints (i.e., the I/O examples) of a synthesis problem,
    return the set of keys that are used in them """
    keys = set()
    for ctr in synt_decl['constraints']:
        keys.update(get_synthesis_keys_aux(ctr['inputs'], 0, max_depth))

    return keys


def get_synthesis_values(synt_decl) -> set[str]:
    values = set()
    for ctr in synt_decl['constraints']:
        values.update(get_synthesis_values_aux(ctr['inputs']))

    return values


def get_synthesis_indices(synt_decl: dict[str:Any]) -> list[int]:
    current_max = 2  # Ensures there are at least 2 values for indices
    for ctr in synt_decl['constraints']:
        n = get_synthesis_max_list_index(ctr['inputs'])
        if n > current_max:
            current_max = n
    return list(range(current_max))


def get_start_symbol(ctrs: list[dict[str, Any]]) -> str:
    if all(isinstance(ctr["output"], bool) for ctr in ctrs):
        start_symb = 'syntBool'
    elif all(isinstance(ctr["output"], list) for ctr in ctrs) or \
            all(isinstance(ctr["output"], dict) for ctr in ctrs) or \
            all(isinstance(ctr["output"], int) for ctr in ctrs) or \
            all(isinstance(ctr["output"], str) for ctr in ctrs):
        start_symb = 'syntJ'
    else:
        raise NotImplementedError(f'Which start symbol for '
                                  f'{[ctr["output"].__class__.__name__ for ctr in ctrs]}')
    return start_symb
