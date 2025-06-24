
from logging import Logger
import os
import re
import subprocess
from typing import List, Tuple
from multilspy.multilspy_types import Position, Range
from veval import VEval, verus
from infer import LLM
from lsp import check_proof_actions, create_lsp
from multilspy.language_server import SyncLanguageServer
from multilspy.lsp_protocol_handler.lsp_types import CodeAction, Diagnostic

def find_hover_ranges(
        diag: Diagnostic,
        code: str
    ) -> List[Range]:
    """
    Find the hover ranges from a Diagnostic object.

    Args:
        diag: The Diagnostic object containing the error information
        code: The source code as a string
    
    Returns:
        A list of Range objects that can be used for hover actions.
    """
    keyword_range = None
    ranges: List[Range] = []
    line_index = diag["range"]["end"]["line"]
    try:
        source_lines = code.splitlines()
        while line_index > 0:
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
    
    return ranges

def debug_with_proof_actions_iter(
        code: str,
        logger: Logger,
        num_iters: int,
        llm: LLM,
        engine: str,
        root_abs_path: str = "./rust_src",
    ) -> Tuple[str, str]:
    """
    Debugging the given code with proof actions iteratively.

    Args:
        file_path: Path to the Rust source file to analyze
        logger: Logger instance for logging messages
        num_iters: Number of iterations to run the debugging process
        llm: LLM instance for inference
        engine: The LLM engine to use for inference
        
    Returns:
        A tuple containing the final code and all debugging actions taken.
    """

    if not os.path.exists(root_abs_path):
        logger.info(f"Creating root directory: {root_abs_path}")
        os.makedirs(root_abs_path, exist_ok=True)
    elif not os.path.exists(root_abs_path + "/Cargo.toml"):
        logger.info(f"Creating Rust project in root directory: {root_abs_path}")
        subprocess.run(
            ["cargo", "init", "--edition", "2021"],
            cwd=root_abs_path,
            check=True,
        )
        # Make sure the edition is set to 2021
    else:
        logger.info(f"Using existing Rust project in root directory: {root_abs_path}")
    
    # Copy the contents of the file to the ./src/main.rs
    src_path = os.path.join(root_abs_path, "src", "main.rs")
    with open(src_path, "w") as f:
        f.write(code)
    logger.info(f"Now writing code to {src_path}")

    lsp = create_lsp(root_abs_path)

    system = """You are a helpful assistant that helps debug Rust code with proof actions. You will be given a piece of Rust code and you need to suggest proof actions to fix the code. Your mission is  to guide the user through applying ProofPlumber Proof Actions to debug Verus proof failures.
Always:

- Ask the user to provide the complete failing `assert` or `ensures` message.
- List the Proof Actions available at that location.
- Recommend a single next step from the workflow (Weakest Precondition Step, Convert Implication into If, etc.).
- After each suggestion, instruct the user to re-verify and report results, then plan the next action.
- When the user confirms the proof passes, help them summarize which condition or variable caused the failure.

Ensure your instructions are concrete, step-by-step, and reference the appropriate Proof Action.

Currently enabled proof actions are listed below:
| Title                                                  | Hover over                                    | Proof action                                                                                                                                                                                                                                                     |
| ------------------------------------------------------ | --------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Move up assertion through statements                   | `assert` keyword                              | Move the current expression "up" one statement in the current function, adjusting it appropriately based on the statement it "moves past" (technically it applies one weakest-precondition step). Currently only handles a subset of available Verus statements. |
| Change implication into if and assert                  | `assert` keyword                              | Convert `assert(A ==> B)` into `if A { assert(B); }`                                                                                                                                                                                                             |
| Introduce Assert forall implies syntax                 | `assert` keyword                              | Take an assertion containing a `forall` quantifier and an implication and introduce a `forall ... implies ... by` statement where the quantified variables are in scope and the proof already assumes the left-hand side of the implication.                     |
| Introduce Assert Forall                                | `assert` keyword                              | Take an assertion containing a `forall` quantifier and introduce a `by` clause where the quantified variables are in scope.                                                                                                                                      |
| Add proof block for this assert                        | `assert` keyword                              | Add a `by` block to an existing assertion.                                                                                                                                                                                                                       |
| Insert assume false for this assert                    | `assert` keyword                              | Add a `by` block containing `assume(false)`.                                                                                                                                                                                                                     |
| Insert failing ensures clauses to the end              | `ensures` keyword                             | Introduce a failing ensures clause as an `assert` statement at the end of the current function                                                                                                                                                                   |
| Split implication in ensures into requires and ensures | `ensures` keyword                             | Take an ensures clause `A ==> B`, and move `A` to the requires clause, leaving `B` in the ensures clause.                                                                                                                                                        |
| Insert failing requires clauses of this function call  | function call                                 | Introduce the function's precondition as an assumption in the caller's context.                                                                                                                                                                                  |
| Reveal function with a new proof block for this assert | function call inside an assertion             | Convert the assertion into an `assert ... by` expression and reveal the selected function's definition inside the `by` block.                                                                                                                                    |
| Reveal function above the asserttion                   | function call inside an assertion             | Add a reveal statement for this function above the current assertion.                                                                                                                                                                                            |
| Split smaller or equal to into separate assertions     | `<=`                                          | Split an assertion of `A <= B` into two assertions: `A < B` and `A <= B`.                                                                                                                                                                                        |
| Insert In-bound predicate for selected seq             | sequence expression inside an `assert ... by` | Adds a clause saying that the sequence index is in bounds.
"""
    instruction = """You are assisting me in debugging a Verus proof failure.  
Follow this generalized workflow:

1. Locate the Failure  
   Identify the first failing proof obligation (`assert` or `ensures`) in the IDE's Problems panel or hover tooltip. 

2. Weakest Precondition Step 
   Apply Weakest Precondition Step to "lift" the failing assertion above the preceding statement, generating an equivalent guard (e.g., `assert B ==> P[x:=Y];`).

3. Convert Implication into If  
   If the lifted guard is `A ==> B`, use Convert Implication into If to transform it into:
   ```rust
   if A { assert B; }
   ```
   This separates the proof of `A` from `B`.
   
4. Inline Preconditions
   For any function calls involved, apply Inline Preconditions to insert `requires` as `assert` or `assume` at the call site, checking caller obligations.

5. Decompose Complex Assertions
   Use Decompose Failing Assertion to split conjunctive or quantified assertions into simpler sub-assertions, and verify each in turn.
    
6. Introduce Assume False
   In branches or proof blocks already known to succeed, apply Introduce Assume False (`assume(false);`) to short-circuit them and focus on the remaining failing paths.
    
7. Insert Failing Postconditions
   For multi-exit methods, use Insert Failing Postconditions to re-insert the original `ensures` as `assert` at each `return`, pinpointing which return path fails.

8. Reveal Function
   Where necessary, apply Reveal Function to unwrap opaque definitions or lemmas (`reveal Foo;`) so the verifier can expand their bodies.
    
9. Iterate Until Root Cause
   After each action, re-verify. Once the proof succeeds, retrace the sequence of transformations to identify the exact variable or condition that violates the obligation.

Now pick a proof action to help you debug this proof.

[IMPORTANT] "Move up assertion through statements " is more helpful for detecting the cause of the error, try this proof action first.

[IMPORTANT] Your output should contain the id of the proof action. If you feel that you have already found out why the proof fails, output -1. And wrap this id in a code block:
```
<id>
```
"""
    exemplars = []

    query = """Current error: <error>
Available Proof Actions: <proof_actions> 
Now debugging the code: <code>"""

    used_actions = ""
    nums = 0
    while nums < num_iters:
        logger.info(f"Debugging iteration {nums + 1}/{num_iters}")

        now_query = query.replace("<code>", code)
        # Find all the diagnostics in the code
        veval: VEval = VEval(code, logger)
        veval.eval()

        diags: List[Diagnostic] = []
        # Get all the hover ranges for the diagnostics
        diag_hovers: List[Tuple[List[Range], Diagnostic]] = []
        err = ""
        
        for i, error in enumerate(veval.verus_errors):
            err += f"Error {i + 1}: {error.get_text()}\n"
            diag = error.get_diagnostic()
            diags.append(diag)
            ranges = find_hover_ranges(diag, code)
            if ranges:
                diag_hovers.append((ranges, diag))

        
        # Change all ' to "
        text = f"{diags}"
        text = text.replace("'", '"')
        print(text)

        action = debug_with_proof_actions(
            diag_hovers,
            err,
            logger,
            lsp,
            llm,
            engine,
            instruction,
            exemplars,
            now_query,
            system,
        )

        with open(src_path, "r") as f:
            code = f.read()

        if action is None:
            logger.info("No action taken, stopping debugging.")
            break
        
        used_actions += f"Iteration {nums + 1}: {action}\n"
        
        nums += 1

    logger.info("Debugging procedure using proof actions have been completed.")

    
    final_code = code
    logger.info(f"Final code after debugging procedure using proof actions:\n{final_code}")

    return final_code, used_actions


def debug_with_proof_actions(
        diag_hovers: List[Tuple[List[Range], Diagnostic]],
        err: str,
        logger: Logger,
        lsp: SyncLanguageServer,
        llm: LLM,
        engine: str,
        instruction: str,
        exemplars: List[str],
        query: str,
        system: str,
    ) -> str | None:
    """
    Debugging the given code with proof actions.

    Args:
        diag_hovers: List of tuples containing ranges and diagnostics for hover actions
        err: The error message from the Verus verifier
        logger: Logger instance for logging messages
        lsp: Language server instance for LSP operations
        llm: LLM instance for inference
        engine: The LLM engine to use for inference
        instruction: Instruction for the LLM to follow
        exemplars: List of example queries for the LLM
        query: Query template for the LLM to fill in with current context
        system: System message for the LLM
        root_abs_path: The absolute path to the root directory of the Rust project
    
    Returns:
        The title of the proof action applied, or None if no action was taken.
    """

    if not diag_hovers:
        logger.info("No diagnostics found.")
        return
    
    code_actions: List[CodeAction] = []

    # Run the LSP server
    with lsp.start_server():
        for (ranges, diagnostic) in diag_hovers:
            print(diagnostic["message"])
            for r in ranges:
                print(r["start"])
                print(r["end"])
                try:
                    result = lsp.request_code_actions(
                        "./src/main.rs",
                        r,
                        [diagnostic]
                    )
                    code_actions.extend(result)
                except Exception as e:
                    logger.error(f"Meet errors during requiring code actions: {e}")
                
    proof_actions: List[CodeAction] = check_proof_actions(code_actions)

    if len(proof_actions) == 0:
        logger.info("No proof actions found.")
        return

    action_lines = [f"{i}: {action["title"]}" for i, action in enumerate(proof_actions)]
    actions_text = "\n".join(action_lines)

    query = query.replace("<error>", err)
    query = query.replace("<proof_actions>", actions_text)
    
    action_id_text = llm.infer_llm(
        engine,
        instruction,
        exemplars,
        query,
        system
    )[0]

    action_id = extract_code_blocks(action_id_text).strip()

    logger.info(f"Choose the {action_id}")

    try:
        action_id = int(action_id)
        logger.info(f"Selected action ID: {action_id}, title = {proof_actions[action_id]['title']}")

        if proof_actions[action_id]["title"] == "Insert failing ensures clauses to the end":
            # Special case for inserting failing ensures clauses
            # TODO
            logger.info("Inserted failing ensures clauses to the end of the code.")
            return proof_actions[action_id]["title"]

        with lsp.start_server():
            is_edit: bool = lsp.apply_code_action(proof_actions[action_id])
            if is_edit:
                logger.info("Code action applied successfully.")
                return proof_actions[action_id]["title"]
            else:
                logger.warning("Code action could not be applied.")
    except Exception as e:
        logger.error(f"Error applying code action: {e}")

def extract_code_blocks(response: str) -> str:
    blocks = re.findall(r'```(?:\w+)?\n([\s\S]*?)```', response)
    if len(blocks) == 0:
        return response
    else:
        return blocks[-1]

def insert_failing_ensures(
        code: str,
        ensures: str,
) -> str:
    """
    Insert the failing ensures clause at the end of the code.

    Args:
        code: The source code as a string
        ensures: The ensures clause to insert
    
    Returns:
        The modified code with the ensures clause inserted.
    """
    
    # TODO
    return code


if __name__ == "__main__":
    import logging
    import json
    from utils import AttrDict
    logging.getLogger("httpx").setLevel(logging.WARNING)
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s %(levelname)s: %(message)s",
        datefmt="%Y-%m-%d %H:%M:%S",
    )
    logger = logging.getLogger(__name__)

    config = json.load(open("config.json"))
    config = AttrDict(config)

    llm = LLM(
        config, logger,
    )

    verus_path = config.verus_path

    code = """use vstd::prelude::*;

fn main() {}

verus!{
spec fn fibo(n: nat) -> nat 
	decreases n
{ 
	if n == 0 { 0 } else if n == 1 { 1 } 
	else { fibo((n - 2) as nat) + fibo((n - 1) as nat) } 
}

proof fn fibo_is_monotonic(i: nat, j: nat)
	requires i <= j,
	ensures fibo(i) <= fibo(j),
    decreases j - i
{  
	if i < 2 && j < 2 {}
	else if i == j {}
	else if i == j - 1 {
		fibo_is_monotonic(i as nat, (j - 1) as nat);
	} else { 
		fibo_is_monotonic(i as nat, (j - 1) as nat);
		fibo_is_monotonic(i as nat, (j - 2) as nat);
	}
    assert(fibo(i) <= fibo(j));
}
}
"""
    verus.set_verus_path(config.verus_path)

    engine = config.aoai_generation_model

    root_abs_path = "./rust_src"

    final_code, used_actions = debug_with_proof_actions_iter(
        code,
        logger,
        3,
        llm,
        engine,
        root_abs_path
    )

    print("Final code after debugging:")
    print(final_code)
    print("Used actions:")
    print(used_actions)
