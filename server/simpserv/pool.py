#coding=utf-8

from multiprocessing import Process, Pipe

class Pool(object):
    def __init__(self):
        super(Pool, self).__init__()
        self.comm_from_child_pool = {}
        self.comm_to_child_pool = {}
        self.process_pool = {}

    def add(self, name, func, args):
        """
        Add a process named name
        """
        # Pipe transport data from child to parent
        from_child_pipe, to_parent_pipe = Pipe()
        # Pipe transport data from parent to child
        from_parent_pipe, to_child_pipe = Pipe()
        # The function args must take two pipe connection as first two arguments
        p = Process(target=func, args=tuple([to_parent_pipe, from_parent_pipe] + list(args)), name=name)
        p.start()
        self.process_pool[name] = p
        self.comm_from_child_pool[name] = from_child_pipe
        self.comm_to_child_pool[name] = to_child_pipe

    def send(self, name, args):
        """
        Send data to process named name
        """
        self.comm_to_child_pool[name].send(args)

    def recv(self, name):
        """
        Try to receive data from process named name, if no data, None returned
        """
        return self.comm_from_child_pool[name].recv() if self.comm_from_child_pool[name].poll() else None
