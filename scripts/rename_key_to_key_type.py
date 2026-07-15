#!/usr/bin/env python3
"""
Rename the `key` type to `key_type` in the HE library.

This script renames the type definition and all usages, but preserves
the mixin field `key` in enc_dec.v.
"""

import re
from pathlib import Path

WORKSPACE = Path(__file__).parent.parent

# Files to process
FILES = [
    "homomorphic_encryption/he_types.v",
    "homomorphic_encryption/enc_dec.v",
    "homomorphic_encryption/benaloh1994/benaloh_party_ahe.v",
    "homomorphic_encryption/paillier1999/paillier_party_ahe.v",
    "homomorphic_encryption/homomorphic_encryption.v",
]

# Replacements for he_types.v (order matters - longer strings first)
HE_TYPES_REPLACEMENTS = [
    # Section names
    ("Section key_def", "Section key_type_def"),
    ("End key_def", "End key_type_def"),
    # Helper definitions (longer names first)
    ("key_eqb_subproof", "key_type_eqb_subproof"),
    ("key_eqb", "key_type_eqb"),
    ("key_eqP", "key_type_eqP"),
    ("key_to_nat", "key_type_to_nat"),
    ("nat_to_key", "nat_to_key_type"),
    ("key_natK", "key_type_natK"),
    ("key_enum", "key_type_enum"),
    ("key_enumP", "key_type_enumP"),
    # Type usages with context
    ("Inductive key", "Inductive key_type"),
    ("hasDecEq.Build key", "hasDecEq.Build key_type"),
    ("isCountable key", "isCountable key_type"),
    ("isFinite.Build key", "isFinite.Build key_type"),
    ("(k1 k2: key)", "(k1 k2: key_type)"),
    ("(a : key)", "(a : key_type)"),
    # Comment update
    ("key type (Dec | Enc)", "key_type type (Dec | Enc)"),
]

# Replacements for enc_dec.v - only the type annotation, not the field name
ENC_DEC_REPLACEMENTS = [
    # The field is `key : party T -> key -> ...`
    # We only change the second `key` (the type)
    ("key : party T -> key ->", "key : party T -> key_type ->"),
]

# Replacements for other files (benaloh, paillier, homomorphic_encryption)
TYPE_USAGE_REPLACEMENTS = [
    # Type in product types
    ("* key *", "* key_type *"),
    # Type annotations
    ("(k : key)", "(k : key_type)"),
    # Comment references
    ("HETypes and key type", "HETypes and key_type type"),
]


def apply_replacements(content: str, replacements: list) -> tuple[str, int]:
    """Apply a list of (old, new) replacements to content."""
    count = 0
    for old, new in replacements:
        if old in content:
            occurrences = content.count(old)
            content = content.replace(old, new)
            count += occurrences
    return content, count


def process_file(filepath: Path, dry_run: bool = False) -> tuple[bool, int]:
    """Process a single file with appropriate replacements."""
    content = filepath.read_text()
    original = content
    total_count = 0
    
    filename = filepath.name
    
    if filename == "he_types.v":
        content, count = apply_replacements(content, HE_TYPES_REPLACEMENTS)
        total_count += count
    elif filename == "enc_dec.v":
        content, count = apply_replacements(content, ENC_DEC_REPLACEMENTS)
        total_count += count
    else:
        # benaloh, paillier, homomorphic_encryption
        content, count = apply_replacements(content, TYPE_USAGE_REPLACEMENTS)
        total_count += count
    
    changed = content != original
    
    if changed and not dry_run:
        filepath.write_text(content)
    
    return changed, total_count


def main():
    import sys
    
    dry_run = "--dry-run" in sys.argv
    
    if dry_run:
        print("DRY RUN - no files will be modified\n")
    
    total_files_changed = 0
    total_replacements = 0
    
    for rel_path in FILES:
        filepath = WORKSPACE / rel_path
        if not filepath.exists():
            print(f"WARNING: {rel_path} not found, skipping")
            continue
        
        changed, count = process_file(filepath, dry_run)
        
        if changed:
            total_files_changed += 1
            total_replacements += count
            status = "would be modified" if dry_run else "modified"
            print(f"{rel_path}: {status} ({count} replacements)")
        else:
            print(f"{rel_path}: no changes needed")
    
    print(f"\nSummary: {total_files_changed} files, {total_replacements} replacements")
    
    if dry_run:
        print("\nRun without --dry-run to apply changes")


if __name__ == "__main__":
    main()
