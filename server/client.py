#coding=utf-8

import time
import socket

HOST = '192.168.1.37'
PORT = 50008

s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
s.connect((HOST, PORT))
to_check = '9,1,n_flash_data_cub,(Sta.HomeProc.CacheData = Sta.CurrData)'
quit = '7,1,n_g2k'
s.sendall('%d,%s'%(len(to_check), to_check))
data = s.recv(1024)
print data
s.close()
