#coding=utf-8

import hashlib, time

from pool import Pool

smv_pool = Pool()

def test(to_parent, from_parent):
    while not from_parent.poll():
        pass
    data = from_parent.recv()
    from_parent.close()
    time.sleep(.6)
    to_parent.send(data)
    to_parent.close()

def do_test():
    smv_pool.add('t', test, ())
    time.sleep(1)
    smv_pool.send('t', [1, 'test!!!'])
    for i in range(0, 11):
        data = smv_pool.recv('t')
        if data:
            print data
        else:
            print i
        time.sleep(.1)


if __name__ == '__main__':
    do_test()