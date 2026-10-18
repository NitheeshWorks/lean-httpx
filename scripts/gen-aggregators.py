#!/usr/bin/env python3
"""Regenerate the layer aggregator modules (LeanHttpx/<Layer>.lean) from the files present."""
import glob, os
os.chdir(os.path.join(os.path.dirname(__file__), '..'))
docs = {'DataTypes': 'Structures and inductives; invariants are fields.',
        'RepoImpl': 'Executable definitions; total.',
        'Specifications': 'The properties, stated in `Prop`.',
        'Proofs': 'The theorems; `Proofs/Verified.lean` bundles them.',
        'APIs': 'The public surface, returning refinements.'}
for d, doc in docs.items():
    mods = sorted(glob.glob(f'LeanHttpx/{d}/*.lean'))
    imps = ''.join(f'import {m[:-5].replace("/", ".")}\n' for m in mods)
    open(f'LeanHttpx/{d}.lean', 'w').write(imps + f'\n/-! # {d}\n\n{doc}\n-/\n')
