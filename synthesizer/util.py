import datetime
import enum
import hashlib
from typing import Any

Solution = dict[str, int | str]
SyntDecl = dict[str:Any]


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
            f'{func_name}_{my_hash(str(keys) + str(values))}'
            f'_{str(depth) + "_" if depth is not None else ""}'
            f'{timestamp}.{extenstion}')


def get_timeout_command_prefix(timeout: int) -> list[str]:
    return ['timeout', '-k', str(timeout + 2), str(timeout + 1)]
