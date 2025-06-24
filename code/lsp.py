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

if __name__ == "__main__":
    main()