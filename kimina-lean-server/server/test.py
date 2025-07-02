import subprocess
import os
import tempfile
import json

HOME_DIR = os.path.expanduser('~')
path_to_mathlib = f'{HOME_DIR}/lean/mathlib4/'
path_to_repl = f"{HOME_DIR}/lean/mathlib4/.lake/packages/REPL/.lake/build/bin/repl"
path_to_lake = f'{HOME_DIR}/.elan/bin/lake'


#outputs = subprocess.run([lake_path, "exe", 'repl'], stdin=temp_file, capture_output=True, text=True, cwd=lean_workspace, timeout=timeout)
            # stdin=subprocess.PIPE,
            # stdout=subprocess.PIPE,
            # stderr=self.error_file,
            # text=True,
            # bufsize=1,  # Line-buffered
            # cwd=path_to_mathlib,  # Set the working directory to 'mathlib4'
            # env=os.environ,  # Inherit environment variables
            # preexec_fn=os.setsid,


error_file = tempfile.TemporaryFile(
            "w+",
        )
# Start the REPL subprocess using lake env
process = subprocess.Popen(
    [path_to_lake, "env", path_to_repl],
    stdin=subprocess.PIPE,
    stdout=subprocess.PIPE,
    stderr=error_file,
    text=True,        
    bufsize=1,       
    cwd=path_to_mathlib,
    env=os.environ,
    preexec_fn=os.setsid  
)

try:
    # Send command to REPL
    command = {"cmd": "import Mathlib.Data.Nat.Basic"}
    print(command)
    json_command = json.dumps(command, ensure_ascii=False) + "\n\n"
    process.stdin.write(json_command)
    process.stdin.flush()

    # Read output line (could loop here for full session)
    response_lines=[]
    while True:
        print('hello101')
        stdout_line = process.stdout.readline()
        print(stdout_line)
        if stdout_line.strip() == "":
            break

        if stdout_line:
            response_lines.append(stdout_line)
    response_str = "".join(response_lines)

    print("REPL response:", response_str)
    response_json = json.loads(response_str)
    print('======================')
    print(response_json)
    # Check stderr for errors
    print("REPL error output:", error_file.read())

finally:
    # Gracefully terminate the subprocess
    process.terminate()
    try:
        process.wait(timeout=2)
    except subprocess.TimeoutExpired:
        os.killpg(os.getpgid(process.pid), signal.SIGKILL)
        print("Force-killed REPL process.")
