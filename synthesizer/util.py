def human_time(total_seconds):
    """ Prints a time in a nice, legible format. """
    if total_seconds < 60:
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
