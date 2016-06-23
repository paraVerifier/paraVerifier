#coding=utf-8

import re
import sys
from copy import deepcopy


def prepare_base(v):
    names = map(
        lambda x: x.split(':')[0].strip(),
        v.strip().strip(';').split(';')
    )
    res = {}
    for n in names:
        res[n] = 'X'
    return res

def prepare_states(bad, base):
    items = bad.strip().split('\n')
    p = re.compile(r'\(([^\(\)]*)=([^\(\)]*)\)', re.S)
    res = []
    for item in items:
        parts = p.findall(item)
        b = deepcopy(base)
        for n, v in parts:
            b[n.strip()] = v.strip()
        res.append(b)
    return res


def prepare(text):
    p = re.compile(r'begindef(.*)enddef\s+beginbad(.*)endbad\s+begingood(.*)endgood', re.S)
    v, bad, good = p.findall(text)[0]
    base = prepare_base(v)
    bad_states = prepare_states(bad, base)
    good_states = prepare_states(good, base)
    return v, bad_states, good_states


def output(filename, v, bad_states, good_states):
    with open(filename + '.info', 'w') as f:
        f.write(v)
    with open(filename + '.csv', 'w') as f:
        keys = bad_states[0].keys()
        f.write(','.join(keys) + ',flag\n')
        for bad in bad_states:
            f.write(','.join(bad[k] for k in keys) + ',0\n')
        for good in good_states:
            f.write(','.join(good[k] for k in keys) + ',1\n')


if __name__ == '__main__':
    filename = sys.argv[1]
    truename = filename.split('.')[0]
    with open(filename, 'r') as f:
        text = f.read()
        v, bad_states, good_states = prepare(text)
        output(truename, v, bad_states, good_states)

