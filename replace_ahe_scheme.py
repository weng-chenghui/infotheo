#!/usr/bin/env python3
"""
Script to replace all occurrences of AHEAlgebra_scheme with AHEAlgebraScheme
"""

import os
import re
from pathlib import Path
from typing import Tuple

def replace_in_files(root_dir: str, file_pattern: str = "*.v", dry_run: bool = False) -> Tuple[int, int]:
    """
    Replace AHEAlgebra_scheme with AHEScheme in all matching files.
    
    Args:
        root_dir: Root directory to search from
        file_pattern: File pattern to match (default: "*.v" for Coq files)
        dry_run: If True, don't actually modify files, just show what would change
    
    Returns:
        Tuple of (files_modified, total_replacements)
    """
    root_path = Path(root_dir)
    if not root_path.exists():
        print(f"Error: Directory {root_dir} does not exist")
        return 0, 0
    
    files_modified = 0
    total_replacements = 0
    
    # Find all matching files
    matching_files = list(root_path.rglob(file_pattern))
    
    if not matching_files:
        print(f"No files matching {file_pattern} found in {root_dir}")
        return 0, 0
    
    print(f"Found {len(matching_files)} file(s) matching {file_pattern}\n")
    
    for file_path in matching_files:
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # Count occurrences
            count = content.count('AHEAlgebra_scheme')
            
            if count > 0:
                # Replace
                new_content = content.replace('AHEAlgebra_scheme', 'AHEScheme')
                
                if not dry_run:
                    with open(file_path, 'w', encoding='utf-8') as f:
                        f.write(new_content)
                    status = "✓ MODIFIED"
                else:
                    status = "⊗ WOULD MODIFY (dry-run)"
                
                print(f"{status}: {file_path.relative_to(root_path)}")
                print(f"  → {count} occurrence(s) replaced")
                
                files_modified += 1
                total_replacements += count
        
        except Exception as e:
            print(f"⚠ Error processing {file_path}: {e}")
    
    return files_modified, total_replacements


def main():
    import sys
    
    # Parse arguments
    dry_run = "--dry-run" in sys.argv or "-n" in sys.argv
    
    root_directory = "/Users/cheng-huiweng/Projects/coq/infotheo"
    
    if dry_run:
        print("=== DRY RUN MODE (no files will be modified) ===\n")
    
    files_changed, total_changes = replace_in_files(root_directory, dry_run=dry_run)
    
    print("\n" + "="*50)
    print(f"Summary: {files_changed} file(s) {'would be' if dry_run else ''} modified")
    print(f"Total replacements: {total_changes}")
    print("="*50)
    
    if dry_run:
        print("\nRun without --dry-run flag to actually modify files:")
        print(f"  python3 {sys.argv[0]}")


if __name__ == "__main__":
    main()
