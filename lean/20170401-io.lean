import system.io
open io

variable [io.interface]

def hello_world : io unit :=
put_str "hello world\n"

#eval hello_world
