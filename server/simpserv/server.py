#coding=utf-8

import socket

def echo(conn, addr):
    data = ''
    try:
        data += conn.recv(1024)
    except socket.timeout, e:
        pass
    conn.sendall(data)
    conn.close()

def start_server(host, port, serv=echo, timeout=5):
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    s.bind((host, port))
    s.listen(1)
    while True:
        conn, addr = s.accept()
        conn.settimeout(timeout)
        serv(conn, addr)