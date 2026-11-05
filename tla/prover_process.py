# Copyright (c) 2026 Eric Spencer. Released under Apache 2.0 license.
"""Bound a prover invocation, including children spawned by its launcher."""
import os
import signal
import subprocess


def run_prover(command, *, cwd, timeout):
    process = subprocess.Popen(command, cwd=cwd, stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, text=True,
                               start_new_session=(os.name == 'posix'))
    try:
        stdout, stderr = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        if os.name == 'posix':
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        else:
            process.kill()
        stdout, stderr = process.communicate()
        raise subprocess.TimeoutExpired(command, timeout, output=stdout, stderr=stderr) from None
    return subprocess.CompletedProcess(command, process.returncode, stdout, stderr)
