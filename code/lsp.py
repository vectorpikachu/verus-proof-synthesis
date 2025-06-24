import re
import subprocess
from typing import List, Tuple
from multilspy import SyncLanguageServer
from multilspy.lsp_protocol_handler.lsp_types import CodeAction, Diagnostic, DiagnosticSeverity
from multilspy.multilspy_config import MultilspyConfig
from multilspy.multilspy_logger import MultilspyLogger

import os
from pprint import pprint

from multilspy.multilspy_types import Position, Range
from parse_errors import parse_verus_error

def split_verus_errors(stderr_output: str) -> List[str]:
    """
    Split multiple Verus error messages from stderr output
    
    Args:
        stderr_output: The complete stderr output from Verus
        
    Returns:
        A list of individual error messages
    """
    # Pattern to identify the start of a new error message
    error_start_pattern = r'(?:^|\n)error:'
    
    # Split the output by error start pattern
    raw_splits = re.split(error_start_pattern, stderr_output)
    
    # First element might be empty or contain non-error output
    if raw_splits and not raw_splits[0].strip():
        raw_splits = raw_splits[1:]
    
    # Reconstruct the error messages with the "error:" prefix
    errors = []
    for i, split in enumerate(raw_splits):
        if split.strip():
            # Don't add "error:" prefix to the first element if it doesn't look like an error message
            if re.search(f'aborting', split):
                continue
            if i == 0 and not re.search(r'--> .*:\d+:\d+', split.split('\n')[0]):
                if 'error:' in stderr_output[:100]:  # Check if 'error:' is at the beginning
                    errors.append(f"error:{split}")
                else:
                    errors.append(split)
            else:
                errors.append(f"error:{split}")
            
    return errors


def run_verus(verus_path: str = "../verus/verus", file_path: str = "./test.rs") -> List[Tuple[List[Range], List[Diagnostic]]]:
    """
    Runs Verus on a given Rust source file and parses the output into
    two lists: Ranges to hover and Diagnostics for errors.

    Args:
        verus_path: Path to the Verus executable
        file_path: Path to the Rust source file to analyze

    Returns:
        out: A list of tuples, each containing:
            - List of Ranges where the error occurred
            - List of Diagnostics with error messages and severity
    """
    cmd = [verus_path, file_path]
    proc = subprocess.run(cmd, capture_output=True, text=True)
    err = proc.stderr

    errors = split_verus_errors(err)

    print(f"Running Verus on {file_path} with command: {' '.join(cmd)}")
    print(f"Verus stderr output:\n{err}")

    ret: List[Tuple[List[Range], List[Diagnostic]]] = []
    for err in errors:
        parsed_error = parse_verus_error(err, file_path)
        if parsed_error[0] and parsed_error[1]:
            # Append the parsed error as a tuple of (ranges, diagnostics)
            ret.append(parsed_error)

    print(f"Parsed {len(ret)} Verus errors.")
    print("Parsed errors:")
    for ranges, diagnostics in ret:
        print(f"Ranges: {ranges}")
        print(f"Diagnostics: {diagnostics}")
    return ret
    

def create_lsp(root_abs_path: str = "./rust_src") -> SyncLanguageServer:
    """
    Creates a SyncLanguageServer instance configured for Rust.

    Args:
        root_abs_path: The absolute path to the root directory of the Rust project

    Returns:
        SyncLanguageServer: An instance of the language server configured for Rust
    """
    config = MultilspyConfig.from_dict({"code_language": "rust"})
    logger = MultilspyLogger()

    root_abs_path = os.path.abspath("./rust_src")

    lsp = SyncLanguageServer.create(config, logger, root_abs_path)
    
    return lsp
                
def check_proof_actions(actions: List[CodeAction]) -> List[CodeAction]:
    """
    Filters the code actions to only include those related to proof generation.

    Args:
        actions: List of CodeAction objects
    Returns:
        List of CodeAction objects that are related to proof generation
    """
    proof_actions = [
        "Apply Induction",
        "Change implication into if and assert",
        "Decompose Failing Assertion",
        "Add proof block for this assert",
        "Insert failing ensures clauses to the end",
        "Insert failing requires clauses of this function call",
        "Insert assume false for this assert",
        "Introduce Assert Forall",
        "Introduce Assert forall implies syntax",
        "Add match pattern for failed assert on enum ",
        "Remove Redundant Assertions",
        "Reveal function above the asserttion",
        "Reveal function with a new proof block for this assert",
        "Insert In-bound predicate for selected seq",
        "Split implication in ensures into requires and ensures",
        "Split smaller or equal to into separate assertions",
        "Move up assertion through statements ",
    ]

    ret: List[CodeAction] = []
    for action in actions:
        if action["title"] in proof_actions:
            ret.append(action)
    return ret

def main():
    lsp = create_lsp()

    # Hint: current root path is "./rust_src"
    with lsp.start_server():
        print("[Open file...]")
        with lsp.open_file("./src/main.rs"):
            text = lsp.get_open_file_text("./src/main.rs")
            print(text)
        print("\n")

        ret_list = run_verus(verus_path="../verus/verus", file_path="./rust_src/src/main.rs")

        print("Having run verus.\n")

        for ret in ret_list:
            ranges, diagnostics = ret
            for r in ranges:
                result = lsp.request_code_actions(
                    "./src/main.rs",
                    r,
                    diagnostics
                )
                print(result)
                result = check_proof_actions(result)
                
                if len(result) > 0:
                    isEdit = lsp.apply_code_action(result[0])
                break

if __name__ == "__main__":
    main()