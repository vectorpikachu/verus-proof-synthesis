from pprint import pprint
import re
from dataclasses import dataclass
from enum import Enum
from typing import List, Tuple, Optional

from multilspy.lsp_protocol_handler.lsp_types import Diagnostic, DiagnosticSeverity, Position, Range

def to_tuple(r: Range) -> Tuple[int, int, int, int]:
    """Convert Range to a hashable tuple for deduplication"""
    return (r['start']['line'], r['start']['character'], 
            r['end']['line'], r['end']['character'])

def deduplicate_ranges(ranges: List[Range]) -> List[Range]:
    """
    Remove duplicate ranges from the list
    
    Args:
        ranges: List of Range objects
        
    Returns:
        A new list with duplicate ranges removed
    """
    # Use a dictionary to track unique ranges
    unique_ranges = {}
    
    for r in ranges:
        # Convert range to tuple for use as key
        key = to_tuple(r)
        
        # Only add if not already in the dictionary
        if key not in unique_ranges:
            unique_ranges[key] = r
    
    # Return the list of unique ranges
    return list(unique_ranges.values())

def parse_verus_error(error_message: str, file_path: str = "./test.rs") -> Tuple[List[Range], List[Diagnostic]]:
    """
    Parse a Verus error message and convert it into Range and Diagnostic objects
    suitable for LSP code actions and hover functionality.
    
    Args:
        error_message: The error message from the Verus verifier
        file_path: Path to the source file (defaults to "./test.rs")
        
    Returns:
        A tuple containing (ranges, diagnostics) where:
        - ranges is a list of Range objects for hover actions
        - diagnostics is a list of Diagnostic objects for the errors
    """
    # Initialize empty lists for results
    ranges = []
    diagnostics = []
    
    # Extract location information using regex
    location_match = re.search(r'--> (.*):(\d+):(\d+)', error_message)
    if not location_match:
        return [], []
    
    # Extract file path, line, and column
    file_path_from_error = location_match.group(1)
    line_number = int(location_match.group(2))
    column_number = int(location_match.group(3))
    
    # Convert to 0-indexed for LSP
    line_index = line_number - 1
    column_index = column_number - 1
    
    # Extract the source line and error indicator
    source_line_match = re.search(rf'{line_number} \|(.*)\n\s*\|\s*([^\n]*)\s+([^\n]+)', error_message)
    if not source_line_match:
        return [], []

    # Get the source line and error indicator
    source_line = source_line_match.group(1)
    indicator_1 = source_line_match.group(2)
    indicator_2 = source_line_match.group(3)
    print(f"{indicator_1}, {indicator_2}")

    # Extract just the carets (^) from the indicator line
    carets_match = re.search(r'(\^+)', indicator_1)
    if not carets_match:
        carets_match = re.search(r'(\^+)', indicator_2)
    
    if not carets_match:
        # If we can't find carets, we can't determine the range
        return [], []
    
    carets = carets_match.group(1)
    
    # Calculate the range of the problematic expression
    start_col = column_index
    end_col = start_col + len(carets)
    
    # Extract the message
    message_match = re.search(r'[Ee]rror:(.+?)\n', error_message)
    prefix = ""
    if message_match:
        prefix = message_match.group(1).strip()
    else:
        # It's not a message. Can be note or warning.
        # Just return empty diagnostics
        return [], []
    
    # Extract the expression from the source line
    expression = ""
    try:
        with open(file_path, 'r') as f:
            source_lines = f.readlines()
            if line_index < len(source_lines):
                full_line = source_lines[line_index]
                expression = full_line[start_col:end_col].strip()
    except Exception:
        # If we can't read the file, use what we can extract from the error message
        expression = source_line.strip()[start_col:end_col].strip()
    
    # Construct the full message
    message = f"{prefix}: {expression}"
    
    # Create the diagnostic range for the expression
    expr_range = Range(
        start=Position(line=line_index, character=start_col),
        end=Position(line=line_index, character=end_col)
    )
    
    # Create the diagnostic
    diagnostic = Diagnostic(
        range=expr_range,
        severity=1,
        message=message
    )
    diagnostics.append(diagnostic)
    
    # Find the assert keyword range for hover actions
    keyword_range = None
    try:
        with open(file_path, 'r') as f:
            source_lines = f.readlines()
            while line_index < len(source_lines) and line_index > 0:
                line = source_lines[line_index]
                
                # Find assert keyword position
                if "assert" in line:
                    assert_match = re.search(r'assert', line)
                    if assert_match:
                        assert_start = assert_match.start()
                        assert_end = assert_match.end()
                        keyword_range = Range(
                            start=Position(line=line_index, character=assert_start),
                            end=Position(line=line_index, character=assert_end)
                        )
                        ranges.append(keyword_range)
                        break
                
                if "ensures" in line:
                    ensures_match = re.search(r'ensures', line)
                    if ensures_match:
                        ensures_start = ensures_match.start()
                        ensures_end = ensures_match.end()
                        keyword_range = Range(
                            start=Position(line=line_index, character=ensures_start),
                            end=Position(line=line_index, character=ensures_end)
                        )
                        ranges.append(keyword_range)
                        break

                # Find other possible hover targets
                # Function calls
                func_calls = re.finditer(r'(\w+)\s*\(', line)
                for match in func_calls:
                    func_name_start = match.start(1)
                    func_name_end = match.end(1)
                    func_range = Range(
                        start=Position(line=line_index, character=func_name_start),
                        end=Position(line=line_index, character=func_name_end)
                    )
                    ranges.append(func_range)
                
                # <= operator
                le_matches = re.finditer(r'<=', line)
                for match in le_matches:
                    le_start = match.start()
                    le_end = match.end()
                    le_range = Range(
                        start=Position(line=line_index, character=le_start),
                        end=Position(line=line_index, character=le_end)
                    )
                    ranges.append(le_range)
                
                # Sequence expressions
                seq_matches = re.finditer(r'\[[^\]]*\]', line)
                for match in seq_matches:
                    seq_start = match.start()
                    seq_end = match.end()
                    seq_range = Range(
                        start=Position(line=line_index, character=seq_start),
                        end=Position(line=line_index, character=seq_end)
                    )
                    ranges.append(seq_range)
                
                line_index-=1
    except Exception as e:
        print(f"Error finding hover ranges: {e}")
    
    # If we couldn't find any hover ranges, add the expression range as a fallback
    if not ranges:
        ranges.append(expr_range)
      
    ranges = deduplicate_ranges(ranges)
    return ranges, diagnostics


# Example usage:
if __name__ == "__main__":
    error_message = """
error: precondition not satisfied
  --> test.rs:31:15
   |
31 |             sum.set(0, sum[0] + a[i]);
   |                        ^^^^^^
   |
  ::: /home/lhz/verus-proof-synthesis/verus/vstd/std_specs/vec.rs:46:9
   |
46 |         i < vec.view().len(),
   |         -------------------- failed precondition

error: precondition not satisfied
  --> test.rs:31:24
   |
31 |             sum.set(0, sum[0] + a[i]);
   |                                 ^^^^
   |
  ::: /home/lhz/verus-proof-synthesis/verus/vstd/std_specs/vec.rs:46:9
   |
46 |         i < vec.view().len(),
   |         -------------------- failed precondition

verification results:: 0 verified, 3 errors
error: aborting due to 5 previous errorsr"""
    
    ranges, diagnostics = parse_verus_error(error_message)
    
    print("Ranges for hover actions:")
    for i, r in enumerate(ranges):
        pprint(r)
    
    print("\nDiagnostics:")
    for i, d in enumerate(diagnostics):
        pprint(d)