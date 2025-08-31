import subprocess
import os
import tempfile
import json

HOME_DIR = os.path.expanduser('~')
path_to_mathlib = f'{HOME_DIR}/lean/mathlib4/'
path_to_repl = f"{HOME_DIR}/lean/mathlib4/.lake/packages/REPL/.lake/build/bin/repl"
path_to_lake = f'{HOME_DIR}/.elan/bin/lake'


with tempfile.TemporaryFile("w+") as error_file:
    process = subprocess.Popen(
        [path_to_lake, "env", path_to_repl],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=error_file,
        text=True,
        bufsize=1,
        cwd=path_to_mathlib,
        env=os.environ,
        preexec_fn=os.setsid,
    )
    command = {"cmd": 'import Mathlib'}
    json_command = json.dumps(command, ensure_ascii=False) + "\n\n"
    process.stdin.write(json_command)
    process.stdin.flush()

    # Read first output line
    res = process.stdout.readline()
    print("REPL response:", res)

    # Check for errors
    error_file.seek(0)
    if errors := error_file.read():
        print("Errors encountered:", errors)

    # Clean up
    process.terminate()


