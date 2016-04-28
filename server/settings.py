#coding=utf-8

HOST = ''
PORT = 50008

# maximum sleep time while there is no connect for a smv process
MAX_SLEEP_TIME = 5

# time out in seconds
TIME_OUT = 5
MU_CHECK_TIMEOUT = 600
MU_CHECK_MEMORY = 1024

# path to NuSMV
SMV_PATH = '/home/fan/Downloads/NuSMV/bin/NuSMV'
MU_PATH = '/home/fan/Downloads/cmurphi5.4.9/src/mu'
MU_INCLUDE = '/home/fan/Downloads/cmurphi5.4.9/include'
GXX_PATH = '/usr/bin/g++'

# path for storing smv files
SMV_FILE_DIR = '/tmp/NuSMV/'
MU_FILE_DIR = '/tmp/cmurphi/'





dirs = [SMV_FILE_DIR, MU_FILE_DIR]

import os

for d in dirs:
    if not os.path.isdir(d):
        os.makedirs(d)
