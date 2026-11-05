#!/usr/bin/env python3
# Copyright (c) 2026 Eric Spencer. Released under Apache 2.0 license.
"""Fetch the pinned official reference parser/model checker, verifying its digest."""
from pathlib import Path
import hashlib
import urllib.request

VERSION = '1.7.4'
SHA256 = '936a262061c914694dfd669a543be24573c45d5aa0ff20a8b96b23d01e050e88'
URL = f'https://github.com/tlaplus/tlaplus/releases/download/v{VERSION}/tla2tools.jar'
DEFAULT_JAR = Path(__file__).resolve().parent / '.tools' / f'tla2tools-{VERSION}.jar'

def verify(path):
    if hashlib.sha256(Path(path).read_bytes()).hexdigest() != SHA256:
        raise ValueError(f'{path}: reference tools SHA-256 mismatch')

def install():
    if DEFAULT_JAR.exists():
        verify(DEFAULT_JAR)
        return DEFAULT_JAR
    with urllib.request.urlopen(URL, timeout=60) as response:
        data = response.read(8 * 1024 * 1024)
    if hashlib.sha256(data).hexdigest() != SHA256:
        raise ValueError('downloaded reference tools SHA-256 mismatch')
    DEFAULT_JAR.parent.mkdir(parents=True, exist_ok=True)
    DEFAULT_JAR.write_bytes(data)
    return DEFAULT_JAR

if __name__ == '__main__':
    print(install())
