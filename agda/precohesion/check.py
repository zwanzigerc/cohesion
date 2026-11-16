#!/usr/bin/env python3
"""Check the public precohesion modules with the Agda 2.9.0 installation on PATH."""
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parent
roots = ["weak-shape-macro", "precohesion-shape0", "higher-shape"]
sources = sorted(module.relative_to(root) for folder in roots for module in (root / folder).glob("*.agda"))
options = ["agda", "--no-libraries", *(part for folder in roots for part in ("-i", folder))]
for module in sources:
    subprocess.run([*options, module], cwd=root, check=True)
print(f"Checked {len(sources)} Agda modules.")
