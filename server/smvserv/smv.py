#coding=utf-8

"""
Functions for checking invariants with NuSMV

@author Yongjian Li <lyj238@gmail.com>
@author Kaiqiang Duan <duankq@ios.ac.cn>
"""

import re
from pexpect import spawn, EOF, TIMEOUT

class SMV(object):
    def __init__(self, smv_path, smv_file, timeout=None):
        super(SMV, self).__init__()
        self.smv_path = smv_path
        self.process = spawn(smv_path + ' -dcx -int -old ' + smv_file)
        self.timeout = timeout
        self.diameter = None
        self.isComputing = False
        self.clear()

    def clear(self):
        self.process.expect([r'.*NuSMV\s+>\s+', EOF, TIMEOUT], timeout=.001)

    def go_and_compute_reachable(self):
        self.clear()
        if not self.diameter and not self.isComputing:
            self.isComputing = True
            self.process.send('go\ncompute_reachable\n')
    
    def go_bmc(self):
        self.clear()
        self.process.send('go_bmc\nset bmc_length 15\n')

    def query_reachable(self):
        if self.diameter:
            return self.diameter
        computed = self.process.expect(
            [r'The\s+diameter\s+of\s+the\s+FSM\s+is ', EOF, TIMEOUT], 
            timeout=0
        )
        if computed == 2:
            return None
        elif computed == 0:
            res = self.process.expect([r'\.\s+NuSMV\s+>\s+', EOF, TIMEOUT])
            if res == 0:
                self.diameter = self.process.before
                return self.diameter
            return '-1'

    def check(self, invariant):
        self.clear()
        self.process.send('check_invar -p \"' + invariant + '\"\n')
        res = self.process.expect([r'--\s+invariant\s+.*\s+is\s+', 'ERROR:\s+', EOF, TIMEOUT],
            timeout=None)
        self.process.expect([r'\s*NuSMV\s+>\s+', EOF, TIMEOUT], timeout=self.timeout)
        if res == 0:
            return self.process.before.strip()
        return '0'
    
    def check_bmc(self, invariant):
        self.clear()
        self.process.send('check_ltlspec_bmc -p "G %s"\n'%invariant)
        res = self.process.expect([
                r'NuSMV\s+>\s+',
                r'ERROR:\s+', EOF, TIMEOUT
            ],
            timeout=None)
        import sys
        sys.stdout.write(', res, %s'%res)
        if res == 0:
            output = self.process.before.strip().split('\n')
            for o in output:
                if o.startswith('-- specification'):
                    return o.strip().split(' ')[-1]
            return "true"
        return '0'

    def exit(self):
        self.process.send('quit\n')
        res = self.process.expect([EOF, TIMEOUT], timeout=self.timeout)
        self.process.terminate(force=True)
        return res == 0

if __name__ == '__main__':
    smv = SMV('/home/duan/Downloads/NuSMV/bin/NuSMV', 'mutualEx.smv')
    print smv.process.before
    print smv.go_and_compute_reachable()
    print smv.check('af')
    print smv.check('n[1] = i')
    print smv.check('n[1] = c -> n[2] != c')
    print smv.exit()

