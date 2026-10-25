The aim is to make the maximum number of modifications to a supplied Lean proof, which is verified as valid, where each modification changes one or two Lean lexical tokens or a complete statement.

A modification (the term mutant is used below) shall not include:
* changing the theorem statement or its type;
* introducing sorry, admit, or new axioms;
* using native_decide, implemented_by, set_option, @[csimp]-style escapes, unsafe, opaque, @[extern], Lean.ofReduceBool, and new macro, notation or instance declarations.
* comments and whitespace, whitespace may change as a side effect of a mutant but does not count as a mutant on its own;
* trivial change whose result does not interact with other proof statements, e.g., adding skip statements

“verified” is defined as no errors, no sorry warning, and the same axioms as the original according to #print axioms.

Create a python program that reads a json file that specifies
* the path to a file containing the Lean proof
* stopping conditions, which are:
  ** target number of accepted mutants;
  ** a maximum number of attempts;
  ** the maximum number of failures in a row;
  ** the overall time budget running out.

The logfile is written to the directory containing the file of the Lean proof.

The file containing the Lean proof is read.  If the proof cannot be completely read the Control Agent lists the file status and terminates.

The program randomly decides which mutant (i.e., small change of one or two Lean lexical tokens; insertions, deletions, reorderings and substitutions are allowed, and for 10% of mutants a complete statement) to make to the Lean proof.

Possible changes include: changing a binary operator to a different binary operator, changing an identifier to another identifier used within the proof.

A unique identifier is assigned to each modified proof.

The modified proof is verified by invoking the Lean theorem prover.

If the verified status is not affected by a mutant, a new mutant is added to the proof.  A new mutant must not reverse the change made by a previous mutant, either directly or indirectly. If the verified status is changed, the mutant is removed and a new mutant created.

A timeout is treated as a change of verified status.

Use a Lean verification oracle to obtain the verified status of the proof.

Lean Beam, https://github.com/leanprover/lean-beam, can be used as the basis for execution.


Add support for using multiple processors to search for acceptable mutations.
An option in the configuration specifies the maximum number of concurrent processes.
The default value is 4.

The behavior of every process is the same as the single process case.
That is, eveyr process has its own mutation and validation iteration of
its private modified proof.

When any process discovers a mutation that does not change its proof's verification status,
information about the mutation is added to a global adata structure that other
processes treat as a source of high priority mutants to try once.

On program termination, one at a time, every process writes its current verified
proof to the log file.

Add support for using multiple processors to search for acceptable mutations.
An option in the configuration specifies the maximum number of concurrent processes.
The default value is 4.

The behavior of every process is the same as the single process case.
That is, eveyr process has its own mutation and validation iteration of
its private modified proof.

When any process discovers a mutation that does not change its proof's verification status,
information about the mutation is added to a global adata structure that other
processes treat as a source of high priority mutants to try once.

On program termination, one at a time, every process writes its current verified
proof to the log file.


Add an option to write log files to a particular director, default "log"
Add an option to specify the quantity of output sent to stdout.  The default sends process id and number of rejected/accepted when accepted increases

