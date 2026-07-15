#!/usr/bin/env python3
"""
Rename script for homomorphic encryption type refactoring.

This script performs systematic renaming of HE types and operations
from the old naming convention to the new one.

Usage:
    python3 scripts/rename_he_types.py [--dry-run]
    
Options:
    --dry-run    Show what would be changed without modifying files
"""

import os
import sys
from pathlib import Path

# Files to process
FILES = [
    # homomorphic_encryption
    "homomorphic_encryption/homomorphic_encryption.v",
    "homomorphic_encryption/benaloh1994/benaloh_party_ahe.v",
    "homomorphic_encryption/paillier1999/paillier_party_ahe.v",
    # dumas2017dual/dsdp
    "dumas2017dual/dsdp/dsdp_interface.v",
    "dumas2017dual/dsdp/dsdp_program.v",
    "dumas2017dual/dsdp/dsdp_correctness.v",
    "dumas2017dual/dsdp/dsdp_program_alt_syntax.v",
    "dumas2017dual/dsdp/dsdp_entropy_trace.v",
]

# Global replacements - ORDER MATTERS (longer strings first to avoid partial matches)
GLOBAL_REPLACEMENTS = [
    # Structure/Type names
    ("Party_AHE_scheme", "AHEAlgebra_scheme"),
    ("Party_HE_types", "HETypes"),
    ("MkPartyHE", "MkHE"),
    
    # Mixin names (HB structures)
    ("isPartyAHE_HomoOps", "isAHEnc"),
    ("isPartyAHE_Algebra", "isAHEAlgebra"),
    ("isPartyHE_EncDec", "isEncDec"),
    
    # Type accessors (phe_ prefix) - longer ones first
    ("phe_E_curry", "enc_curry"),
    ("phe_party", "party"),
    ("phe_msg", "plain"),
    ("phe_rand", "rand"),
    ("phe_cipher", "cipher"),
    ("phe_enc", "party_cipher"),
    ("phe_pkey", "pkey"),
    ("phe_E", "enc"),
    ("phe_K", "key"),
    ("phe_D", "dec"),
    
    # Operation names (pahe_ prefix) - longer ones first
    ("pahe_Emul_addE", "Emul_addE"),
    ("pahe_Emul_addM", "Emul_addM"),
    ("pahe_Epow_mulM", "Epow_mulM"),
    ("pahe_Emul_assoc", "Emul_assoc"),
    ("pahe_Emul_comm_cipher", "Emul_comm_cipher"),
    ("pahe_Emul_id", "Emul_id"),
    ("pahe_enc_cipher", "enc_cipher"),
    ("pahe_rand_unit", "rand_unit"),
    ("pahe_rand_pow", "rand_pow"),
    ("pahe_Emul", "Emul"),
    ("pahe_Epow", "Epow"),
]

# Benaloh-specific replacements
BENALOH_REPLACEMENTS = [
    # Type bundle
    ("Benaloh_Party_HE_types", "Benaloh_HETypes"),
    
    # HB instance names
    ("Benaloh_isPartyAHE_HomoOps", "Benaloh_isAHEnc"),
    ("Benaloh_isPartyAHE_Algebra", "Benaloh_isAHEAlgebra"),
    ("Benaloh_isPartyHE_EncDec", "Benaloh_isEncDec"),
    
    # Definition prefixes - longer ones first
    ("benaloh_phe_dec_correct", "benaloh_dec_correct"),
    ("benaloh_phe_E", "benaloh_enc"),
    ("benaloh_phe_K", "benaloh_key"),
    ("benaloh_phe_D", "benaloh_dec"),
    
    ("benaloh_pahe_Emul_addM", "benaloh_Emul_addM"),
    ("benaloh_pahe_Epow_mulM", "benaloh_Epow_mulM"),
    ("benaloh_pahe_Emul_assoc", "benaloh_Emul_assoc"),
    ("benaloh_pahe_Emul_comm_cipher", "benaloh_Emul_comm_cipher"),
    ("benaloh_pahe_Emul_comm_same_party", "benaloh_Emul_comm_same_party"),
    ("benaloh_pahe_Emul_id", "benaloh_Emul_id"),
    ("benaloh_pahe_enc_cipher", "benaloh_enc_cipher"),
    ("benaloh_pahe_rand_unit", "benaloh_rand_unit"),
    ("benaloh_pahe_rand_pow", "benaloh_rand_pow"),
    ("benaloh_pahe_Emul", "benaloh_Emul"),
    ("benaloh_pahe_Epow", "benaloh_Epow"),
]

# Paillier-specific replacements
PAILLIER_REPLACEMENTS = [
    # Type bundle
    ("Paillier_Party_HE_types", "Paillier_HETypes"),
    
    # HB instance names
    ("Paillier_isPartyAHE_HomoOps", "Paillier_isAHEnc"),
    ("Paillier_isPartyAHE_Algebra", "Paillier_isAHEAlgebra"),
    ("Paillier_isPartyHE_EncDec", "Paillier_isEncDec"),
    
    # Definition prefixes - longer ones first
    ("paillier_phe_dec_correct", "paillier_dec_correct"),
    ("paillier_phe_E", "paillier_enc"),
    ("paillier_phe_K", "paillier_key"),
    ("paillier_phe_D", "paillier_dec"),
    
    ("paillier_pahe_Emul_addM", "paillier_Emul_addM"),
    ("paillier_pahe_Epow_mulM", "paillier_Epow_mulM"),
    ("paillier_pahe_Emul_assoc", "paillier_Emul_assoc"),
    ("paillier_pahe_Emul_comm_cipher", "paillier_Emul_comm_cipher"),
    ("paillier_pahe_Emul_comm_same_party", "paillier_Emul_comm_same_party"),
    ("paillier_pahe_Emul_id", "paillier_Emul_id"),
    ("paillier_pahe_enc_cipher", "paillier_enc_cipher"),
    ("paillier_pahe_rand_unit", "paillier_rand_unit"),
    ("paillier_pahe_rand_pow", "paillier_rand_pow"),
    ("paillier_pahe_Emul", "paillier_Emul"),
    ("paillier_pahe_Epow", "paillier_Epow"),
]


def apply_replacements(content: str, replacements: list[tuple[str, str]]) -> str:
    """Apply a list of (old, new) replacements to content."""
    for old, new in replacements:
        content = content.replace(old, new)
    return content


def process_file(filepath: Path, dry_run: bool = False) -> tuple[bool, int]:
    """
    Process a single file with appropriate replacements.
    
    Returns:
        (was_modified, replacement_count)
    """
    if not filepath.exists():
        print(f"  WARNING: File not found: {filepath}")
        return False, 0
    
    content = filepath.read_text()
    original = content
    
    # Determine which replacements to apply based on filename
    filename = filepath.name
    
    if filename == "benaloh_party_ahe.v":
        # Apply Benaloh-specific first (more specific), then global
        content = apply_replacements(content, BENALOH_REPLACEMENTS)
        content = apply_replacements(content, GLOBAL_REPLACEMENTS)
    elif filename == "paillier_party_ahe.v":
        # Apply Paillier-specific first (more specific), then global
        content = apply_replacements(content, PAILLIER_REPLACEMENTS)
        content = apply_replacements(content, GLOBAL_REPLACEMENTS)
    else:
        # Just global replacements
        content = apply_replacements(content, GLOBAL_REPLACEMENTS)
    
    # Count changes (approximate - count lines that differ)
    orig_lines = set(original.splitlines())
    new_lines = set(content.splitlines())
    changed_lines = len(orig_lines.symmetric_difference(new_lines))
    
    was_modified = content != original
    
    if was_modified and not dry_run:
        filepath.write_text(content)
    
    return was_modified, changed_lines


def main():
    dry_run = "--dry-run" in sys.argv
    
    # Determine workspace root (script is in scripts/ subdirectory)
    script_dir = Path(__file__).parent
    workspace_root = script_dir.parent
    
    if dry_run:
        print("=== DRY RUN MODE - No files will be modified ===\n")
    
    print(f"Workspace: {workspace_root}\n")
    print("Processing files:\n")
    
    total_modified = 0
    total_changes = 0
    
    for rel_path in FILES:
        filepath = workspace_root / rel_path
        print(f"  {rel_path}...", end=" ")
        
        modified, changes = process_file(filepath, dry_run)
        
        if modified:
            total_modified += 1
            total_changes += changes
            print(f"MODIFIED (~{changes} lines changed)")
        else:
            print("no changes")
    
    print(f"\n{'Would modify' if dry_run else 'Modified'}: {total_modified} files")
    print(f"Approximate lines changed: {total_changes}")
    
    if dry_run:
        print("\nRun without --dry-run to apply changes.")
    else:
        print("\nDone! Remember to verify changes compile: make -j4")


if __name__ == "__main__":
    main()
