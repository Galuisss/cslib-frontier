# RAM variants and allocating pointer machines

## Unbounded natural registers

[CslibFrontier/Computability/RAM/Defs.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/RAM/Defs.lean) defines `Cslib.RAM` over the upstream URM register store. Registers hold arbitrary natural numbers; inputs occupy the initial registers, the remainder starts at zero, and register zero is the output. Instructions include constants, addition, truncated subtraction, multiplication, indirect loads/stores and a positive branch. Falling past the program list halts; subsequent clocked runs stutter. A partial evaluator and relational execution are linked by determinism and run/evaluation correspondence [cslib-frontier][complexitylib].

This is an adaptation of Cook–Reckhow-style RAM, not a literal copy: its data are naturals rather than integers, multiplication is supplied, and the initial register input is a convention rather than charged finite-alphabet I/O. Those choices matter before comparing complexity classes [cookreckhow73][cookreckhow73].

[CslibFrontier/Computability/RAM/Cost.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/RAM/Cost.lean) makes the charge function explicit. `unitCost` assigns one to a step, while `logCost` uses bit lengths of relevant operands/addresses; `bitLength 0 = 1`. `HaltsWithResultInTime` and `ComputesInTime` quantify costed successful runs. `RAM/Input` adds explicit input encodings and preparation programs when a comparison needs to charge them.

The cost distinction is witnessed by [repeatedSquaring](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/RAM/Squaring.lean#L74), an eight-instruction program computing `2^(2^k)`. `time_unitCost_repeatedSquaring` gives its exact unit-step cost. `two_pow_lt_of_computesInTime_logCost` and `exists_mul_pow_lt_of_computesInTime_logCost` force exponential output-bit-length cost under the logarithmic convention and rule out each polynomial bound in `k`. The result is a concrete warning against treating unit-cost unbounded multiplication as ordinary bit computation.

## Generic partial-operation RAM

[Model](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/GenericRAM/Defs.lean#L64) supplies types of values, addresses and configurations; literal syntax; operation/test signatures; partial evaluation; partial address extraction; produced-value admissibility; move validity; and control-label validity. The shared interpreter supplies finite registers, indirect total memory, program counter, explicit halt and a separate fault outcome.

Separating literal syntax from values lets an instance restrict program constants; the generic `Const` type and its interpretation remain arbitrary. The natural/rational restriction belongs to the algebraic instances below. Partial address extraction makes conversion to an address explicit and allows it to fail; the chosen model supplies that conversion. The generic interpreter itself chooses neither binary encodings nor an implementation of primitive operations. Unit-step semantics and `Executes.unique` establish deterministic execution for a chosen interpretation, not effective computability of all interpretations.

Word-RAM maps into this core step for step. `WordRAM.step_toGeneric`, `run_toGeneric` and `executes_toGeneric_iff` preserve its concrete semantics. This is more than a resemblance between definitions: it permits generic execution metatheory to be reused without changing instruction counts.

## Exact algebraic instances

[CslibFrontier/Computability/GenericRAM/Algebraic.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/GenericRAM/Algebraic.lean) uses tagged values `Nat ⊕ K`. Only the natural arm can address memory. A width bounds natural words and control labels by `2^w`; exact field values are not bounded that way. Word arithmetic faults on overflow/underflow or zero divisor; field division by zero faults. There is a word-to-field conversion and no reverse conversion, floor, square root or transcendental operation.

Literal symbols are natural words or rationals. A rational denominator that maps to zero in positive characteristic faults. `Algebraic.real` adds exact real comparison and noncomputable mathematical semantics; `Algebraic.primeField` uses executable prime-field arithmetic and equality without an order test on the field arm. Both use the generic one-instruction currency.

The local documentation maps the real instance to Erickson–van der Hoog–Miltzow §6.1. Its tagged single memory differs from that source's separate word/real arrays, and checked arithmetic differs from modular word arithmetic. The primary source explicitly distinguishes finite word addresses from exact real storage; the formalization's modifications should remain visible [erickson24][erickson24]. No bit-cost or exact-real Turing implementation is asserted.

## Native representation and sparse memory

[CslibFrontier/Computability/GenericRAM/Native.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/GenericRAM/Native.lean) introduces `Model.Encoding` and `Model.NativePrimitives`. Each value/address/configuration encoding is faithful, and scalar operations, tests, literal checks and validity conditions receive native certificates. Configuration and operands are runtime inputs. The source instruction is fixed for the scalar certificate, so constants may depend on the fixed source program.

`NativeCertificate` records an actual finite machine with independent time, workspace and encoded-output-size bounds. These are ingredients for a simulator, not a blanket theorem that every generic RAM is efficient.

[CslibFrontier/Computability/GenericRAM/SparseMemory/Basic.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/GenericRAM/SparseMemory/Basic.lean) represents memory by a default value and finite association list. The encoded object is that finite representation, not the mathematical total function. [CslibFrontier/Computability/GenericRAM/Simulation/Turing.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/GenericRAM/Simulation/Turing.lean), `Simulation/Run` and `Simulation/Degree` compile the finite transition and iterate it with explicit costs. Initialization and extracting an answer remain additional obligations. The Word-RAM specialization discharges those obligations with fitting word widths and a chosen step budget.

## Allocating pointer-machine foundation

Import `CslibFrontier.Computability.PointerMachine.Defs` for `Cslib.PointerMachine`.
That file is the whole model and contains no proofs. `PointerMachine.Basic` supplies
invariants and resource bounds.

`Model` gives one type of data values, a distinguished `undefined` value, and named
binary operations and predicates with total interpretations. `Layout` fixes the number
of pointer registers, data registers, pointer fields and data fields. The model, the
layout and the finite instruction list are fixed independently of input size. A basis
with several kinds of data uses a sum type whose operations return `undefined` on
operands of the wrong kind.

`State M L` holds a control label, the two register banks and `heap`, the list of all
records in order of creation. A `Pointer` is null or the position of a record in that
list. Positions are natural numbers, but no instruction takes or returns one: programs
obtain pointers only by copying a register, loading a pointer field of a record that a
register specifies, or creating a record. `Instr.effect_provenance` states this.
Heap placement cannot affect execution: the embedding theorem below makes this precise.

`Instr.effect` gives each instruction's effect on registers and records, and
`Instr.next` the label that follows. Both are total. A load or store through null does
nothing. A new record has null pointer fields and `undefined` data fields. Control
labels are zero-based. `step` is undefined at `halt` and outside the program;
`Executes` requires the final label to hold `halt`.

`State.Valid` requires every nonnull pointer in a register or record to specify a
record. It allows cycles, sharing and unreachable records. Applications supply valid
input states, with preparation cost separate; `Runs.valid` and `Executes.valid` preserve the hypothesis.
Outside valid states a pointer that specifies no record acts like null until a
later creation gives it one; `Instr.create_fresh` shows that in a valid state no
register or record already holds the pointer that `create` returns.

`Runs` reuses CSLib's `Relation.RelatesInSteps`; `Executes` also charges the final halt.
Each instruction costs one unit, including a data primitive or a creation.
Space is `heap.length`: initial records plus creations, including unreachable
records. There is no deletion or garbage collection. `Runs.length_le` (or `Executes.length_le` for a halting run) bounds
space by initial records plus instructions executed. These are instruction
and record measures, not bit-time, bit-space, or host allocation costs. Changing the
primitives changes what one instruction can accomplish.

`PointerMachine.Data` shows that a predicate on data which holds of `undefined` and is
closed under the operations is preserved by execution. `PointerMachine.Renaming` supplies identity, inverse and composition of data renamings.
`Executes.rename_iff` shows that a permutation of the data commuting with the primitives commutes with execution,
with the same cost.

For address changes, import
[`CslibFrontier.Computability.PointerMachine.Simulation`](../../CslibFrontier/Computability/PointerMachine/Simulation.lean).
`State.Embeds f x y` requires valid states, identical control and data, and an injective
map from the allocated source addresses into the target heap. Registers and record
fields follow that map. The target may contain extra records, including incoming links
to the embedded records; the map need only be injective on allocated source addresses.
`Runs.embed` and `Runs.of_embed` transport runs in both directions with the exact same
number of instructions. `Executes.embed` and `Executes.of_embed` include the halt charge.
Their final embedding extends the initial map on every previously allocated source
address: a creation maps the fresh source address to the fresh target address.
`State.Embeds.halts_iff` gives equivalence of successful termination at any specified cost.
These results allow reordering and extra memory, but do not yet state a separation
theorem for independently evolving components or a correspondence with Tarjan's traps.

For symbols, the carrier type alone does not establish opacity: an operation from
symbols to integers would reveal an encoding. The protected-symbol instance
is `Symbols.model` from `CslibFrontier.Computability.PointerMachine.Symbols`.
Its values are undefined, a symbol or an integer. It supplies equality of data,
integer constants, addition and subtraction, and integer order; arithmetic on a symbol returns
`undefined`. Abstract symbols and integer counters can therefore coexist in one
record, as they do in Tarjan's weighted-union example. `Symbols.hasSymbol_of_executes`
and `Symbols.symbolRenaming` state that programs neither produce symbols nor tell
them apart except by equality.

After the [standard setup](../workflows/getting-started.md), check the
[clients](../../CslibFrontierTests/PointerMachine.lean) with
`lake build CslibFrontierTests.PointerMachine --wfail --iofail`.
They run one program on symbols, integers and pointers with exact instruction
accounting, initialize integer fields from reset data registers, and chase parent links in a
loop using pointer equality and copying. They also cover null access, new records and invalid
pointers. The clients
are model examples, not a verified union-find implementation or lower bound.
The [embedding client](../../CslibFrontierTests/PointerMachineEmbedding.lean), checked with
`lake build CslibFrontierTests.PointerMachineEmbedding --wfail --iofail`, embeds a two-node
chain into a reordered four-node heap with extra incoming links. It checks fresh allocation,
preservation of old address images, and a loop whose exact cost remains 15 instructions.

To compile to the standard word RAM, import
[`CslibFrontier.Computability.PointerMachine.WordRAM.Correctness`](../../CslibFrontier/Computability/PointerMachine/WordRAM/Correctness.lean)
and use the namespace `Cslib.PointerMachine.WordRAM`. Supply `Scalars M L`: an injective
single-word encoding of data, actual word-RAM programs for the scalar operations and tests,
and proofs of their values, frames, admissibility conditions and instruction bounds.
These hypotheses concern scalar routines only. The compiler implements pointer access,
null behavior, field updates, allocation and control flow itself.

`S.compile code` is a finite standard-word-RAM program. Each source instruction has a fixed-size
code block, and branches jump directly to the corresponding block. A node occupies
`stride L = max 1 (L.ptrFields + L.dataFields)` words; null is zero and node `a` has
address `1 + stride L * a`. This address arithmetic belongs to the compiled implementation.
The source instruction set still has no address arithmetic.

`S.executes_compile` starts with `encodeState S.encode x`, the canonical encoding of the
source state, at target label `S.blockSize code * x.pc`. If the valid source state executes
successfully in `time` instructions, the theorem produces a target run ending at a state
representing the entire source result, followed by a halt returning zero. The target run plus
halt costs at most `S.overhead code * time`. The constant is computed from the fixed source
program, layout and supplied scalar instruction bounds. `S.runs_compile` also handles finite
runs from any represented state, and `S.length_compile` gives the compiled program length.

The caller proves `Fits` at every source instruction boundary and the scalar admissibility
conditions for calls that execute. `Fits` records named bounds (`free`, `data`, `heapData`)
for the next-free address, scalar registers and scalar heap fields; validity then bounds all
pointer words and occupied field addresses. The compiler
proofs discharge intermediate address bounds and new-record initialization internally.
`bounded_encodeState` proves that the canonical target registers and memory contain fitting
words. Input-list preparation and output decoding are outside this theorem: it is a simulation
from encoded machine states. The theorem bounds instruction time, not scalar routines'
transient workspace; their memory frame constrains their final memory only. It does not prove
fault correspondence, or supply encodings and scalar implementations for every possible `Model`.

The [compiler client](../../CslibFrontierTests/PointerMachineWordRAM.lean) supplies concrete
natural-number scalar routines and checks allocation, field access, arithmetic, branching and
looping. Build it with
`lake build CslibFrontierTests.PointerMachineWordRAM --wfail --iofail`.

GenericRAM was assessed for reuse: its `evalOp` receives only register operands and
fixed configuration, and `Data.mem` has no allocation state. Its `admissible` and
`validMove` checks cannot consult a changing heap. Tagging values and restricting
`address` would prevent scalar address conversion but would not establish provenance
or fresh allocation. The pointer-machine module supplies its own small-step
instruction semantics while reusing the common exact-step relation and its resource
lemma. A common control engine or certified GenericRAM lowering would need a separate
semantic preservation argument.

The sources are [Tarjan 1977](../sources.md#tarjan77), §2, pp. 4–7, and
[Tarjan 1979](../sources.md#tarjan79),
§2, pp. 111–112: separate data and pointer registers and fields, identical records,
access by explicit reference only, binary data operations and predicates, record
creation, null access doing nothing, a final halt, and one unit per instruction.
The formalization differs in four ways. Labels start at zero, and running past the
last instruction is not a successful halt. The source fills every field of a new
record with a special undefined value; here pointer fields are null and only data
fields are undefined. The source has a built-in equality test on data; here equality
is a predicate the model may supply. Tarjan halts on an attempted use of an undefined register or field, while allowing it to
be overwritten. This model instead permits reads of null initial pointer fields and treats
undefined data through total, model-chosen operations and predicates. For example,
`Symbols.evalTest .eq .undefined .undefined` is true. This is a semantic relaxation, not
a proved equivalence: source-faithful upper-bound programs must initialize slots before
reading them. Transferring a lower bound also requires a correspondence argument; none
is supplied here. No claim of a step-exact translation of
every source program, or of equivalence with pure atomistic SMM/KUM models, is made.

Tarjan's union-find application adds assumptions (3.1)–(3.5), pp. 113–114. Element and
set identities are equality-only symbols; the initial memory is separated by sets;
and each invocation resets other registers and supplies designated input pointers.
The paper explains that symbol opacity prevents packing a whole set into one datum
and moving it at unit cost. These application assumptions are essential to the
stated lower bound and are not bundled into the general machine. The weighted-union
algorithm, pp. 114–115, combines symbol identities, integer sizes, and parent pointers.
The current foundation does not prove that algorithm or Tarjan's lower bound.

## Linked BST and AVL operations

Import [`CslibFrontier.DataStructure.AVLTree.PointerMachine`](../../CslibFrontier/DataStructure/AVLTree/PointerMachine.lean)
for an instruction-counted search of an already represented AVL tree.
`SearchTree.PointerMachine` adapts the left/right/parent layout from Stefan Langerman's
earlier `lean-bst` development to Frontier's `BinaryTree`. Ghost labels describe node addresses and all scalar fields;
they are proof data, not integer pointers available to the program. The heap may contain
unrelated records.

`SearchTree.PointerMachine.search_correct` proves that one fixed eleven-instruction program
agrees with `SearchTree.contains`. It takes at most `6 * searchVisits + 3` executed instructions,
including null checks, comparisons, branches and halt. Register zero supplies the root pointer
and query (in the pointer and data banks respectively). The output cursor is null on failure;
on success the theorem identifies the node in the mathematical tree and preserves its entire
scalar payload. Only cursor register zero, null pointer register five and scalar temporary
register one may change. The heap is unchanged.

`AVLTree.search_correct` combines this program with the existing AVL height theorem, giving
at most `12 * Nat.log 2 (card + 1) + 3` instructions. A model-supplied scalar predicate must
implement strict comparison. The [checked client](../../CslibFrontierTests/PointerMachineSearchTree.lean)
covers successful and unsuccessful searches, an empty root, metadata, client registers and
unrelated heap records. Run it with
`lake build CslibFrontierTests.PointerMachineSearchTree --wfail --iofail`.

Import the linked-tree
[`Allocation`](../../CslibFrontier/DataStructure/SearchTree/PointerMachine/Allocation.lean) and
[`Update`](../../CslibFrontier/DataStructure/SearchTree/PointerMachine/Update.lean) modules
for separately charged mutation primitives:
`SearchTree.PointerMachine.allocate_correct` initializes a fresh leaf in `extra + 4` instructions,
preserving the old heap; `Represents.append` preserves existing tree representations.
`storeData_correct` proves a scalar-field write in two instructions including halt, with
the register and unrelated-record frame. `keys_updateData` shows that payload and metadata
writes preserve the key tree. Allocation does not attach the new leaf to its parent.
The [allocation client](../../CslibFrontierTests/PointerMachineAllocation.lean) checks arbitrary
key/payload initialization, old-tree preservation, and allocation into an empty heap.

The [`Rotation`](../../CslibFrontier/DataStructure/SearchTree/PointerMachine/Rotation.lean)
module implements both subtree rotations in ten instructions, including halt.
`rotateRight_represents` and `rotateLeft_represents` prove the recursive representation,
including pivot and middle-subtree parent links, assuming distinct node addresses.
They preserve nonscratch registers and records outside the pivots and middle root;
address distinctness survives both rotations. These programs leave cached heights and
the external parent's child link unchanged.

[`Reconnect`](../../CslibFrontier/DataStructure/SearchTree/PointerMachine/Reconnect.lean)
repairs that external link in seven instructions, or the overall root register in five.
[`Height`](../../CslibFrontier/DataStructure/SearchTree/PointerMachine/Height.lean) recomputes
a root's cached height in nine instructions from correct child caches, using explicit scalar
zero and maximum-plus-one operations. The
[AVL representation bridge](../../CslibFrontier/DataStructure/AVLTree/PointerMachine/Representation.lean)
matches keys **and cached heights** to Frontier's existing `AVLTree`; its
`recomputeHeight_mkNode` theorem proves that height repair implements the existing `mkNode`.

[`Blocks`](../../CslibFrontier/Computability/PointerMachine/Blocks.lean) assembles certified
routines into a single finite program: `Executes.inBlock` relocates jumps and turns each
halt into a continuation jump at the same instruction cost. Sequencing adds one final halt;
branch selection adds a test and final halt. This is verified block composition, not an
automatic compiler from arbitrary Lean functions.
The [ghost context](../../CslibFrontier/DataStructure/SearchTree/PointerMachine/Context.lean)
records ancestors and siblings for whole-tree proofs; it is not a physical machine stack.
Its parent-navigation theorem charges two instructions, including halt.

[`Frame`](../../CslibFrontier/Computability/PointerMachine/Frame.lean) derives scalar-field
preservation from program syntax: if no instruction allocates or stores a selected field,
every run preserves that field at every address, even when pointer links change. The
`addresses` footprint and `AddressesDistinct.node_iff` support lifting subtree changes
through ancestor contexts, deriving separation from the original tree's distinct addresses.

The [AVL rotations](../../CslibFrontier/DataStructure/AVLTree/PointerMachine/Rotation.lean)
compose pointer rewiring with both height repairs: each direction takes 39 instructions
and matches the corresponding existing `AVLTree.rotateLeft` or `rotateRight` result.
[`balance_correct`](../../CslibFrontier/DataStructure/AVLTree/PointerMachine/Balance.lean)
implements all five cases of `AVLTree.balance` in at most 121 instructions, including the
nested rotations and their internal reconnection. It preserves the subtree's addresses,
all nonheight payload fields and unrelated heap records; register six retains the former
root for external reconnection. The
[balance client](../../CslibFrontierTests/AVLPointerMachineBalance.lean) exercises every case
with stale root heights and additional payload fields.

[`reconnect_context`](../../CslibFrontier/DataStructure/SearchTree/PointerMachine/ReconnectContext.lean)
lifts a local replacement to a complete linked tree by running the actual reconnection
program. Its premises describe the original whole tree, the replacement subtree, and the
unchanged exterior. Its conclusion establishes the updated whole tree and root register,
address separation, and preservation of every scalar field. Ghost ancestor contexts bound
upward traversal by the original tree height without adding a machine stack.

[`seek_correct`](../../CslibFrontier/DataStructure/SearchTree/PointerMachine/Seek.lean)
retains the missing key's parent and comparison path in at most `7 * searchVisits + 4`
instructions. [`insertLeaf_correct`](../../CslibFrontier/DataStructure/SearchTree/PointerMachine/InsertLeaf.lean)
allocates and attaches a complete leaf at that vacant child link, or at the empty root,
in `extra + 9` instructions. A successful search can keep the existing node and its payload.

Import [`AVLTree.PointerMachine.Insert`](../../CslibFrontier/DataStructure/AVLTree/PointerMachine/Insert.lean)
for complete insertion. `insert_correct` proves that one finite program searches, allocates
and attaches a leaf on a miss, and balances every ancestor while following parent pointers.
Its result matches the existing `AVLTree.insert`, including height caches. The bound is
`141 * cachedHeight + extra + 31`, hence `282 * Nat.log 2 (card + 1) + extra + 31` for a valid
input AVL tree. All navigation, scalar operations, allocation, continuation jumps and halt
are charged. At most one node is allocated; existing addresses and nonheight payloads survive.
An existing key keeps its payload: this is set insertion, with value updates available through
the separate scalar-field store primitive. The
[insertion client](../../CslibFrontierTests/AVLPointerMachineInsert.lean) checks empty input,
duplicates, single and double rotations, fresh payloads and non-height scalar fields of
unrelated records. The insertion contract does not assert preservation of pointer or height
fields in unrelated records.

For an actual standard word-RAM implementation with natural keys and scalar fields, import
[`AVLTree.WordRAM`](../../CslibFrontier/DataStructure/AVLTree/WordRAM.lean).
`AVLTree.WordRAM.insert_correct` composes the concrete insertion program with the pointer
compiler and the [certified natural scalar basis](../../CslibFrontier/Computability/PointerMachine/WordRAM/Natural.lean).
The scalar routines use ordinary word-RAM instructions: zero costs one instruction,
maximum-plus-one and the height-gap test at most five, and order comparisons at most three.
The gap test uses subtraction and handles a maximal-word second operand without overflowing.
Operand/destination aliasing is covered by the certificates.

Let `T = 282 * Nat.log 2 (card + 1) + extra + 31`, and let `B` bound all initial scalar
registers and heap fields. It suffices that both `B + T` and
`nodeAddr L (initialHeap.length + T)` fit the chosen word width. These conservative bounds
cover temporary values and addresses throughout the source run; the
[natural simulation theorem](../../CslibFrontier/Computability/PointerMachine/WordRAM/NaturalSimulation.lean)
derives the intermediate fit and admissibility conditions. The compiled execution costs at
most `(4 * extra + 22) * T`, including halt, and represents the same insertion result and
payloads. The target starts with the canonical encoded input heap; input encoding is not
charged. The [composed client](../../CslibFrontierTests/AVLWordRAM.lean) discharges every
hypothesis for an eight-bit execution inserting a key with a separate payload into an empty tree.

The general pointer implementation allows other scalar models satisfying the specified
operations and comparisons. Its global height-comparison contracts require an infinite
source scalar domain; the natural instantiation above implements bounded executions of that
domain using finite words. This does not identify arbitrary scalar models with the word RAM.

### Compiling the standard word RAM to pointer machines

Import
[`WordRAM.PointerMachine.Simulation`](../../CslibFrontier/Computability/WordRAM/PointerMachine/Simulation.lean)
and use `Cslib.WordRAM.PointerMachine.executes_input`. Given a successful deterministic
`WordRAM.Executes w p ⟨0, Data.init input⟩ v n`, it constructs a halting execution of the finite
program `compile w p`, returning `v` in scalar register three. If the input has `N` words,
the execution uses at most `N + n` records and
`n * (294 * Nat.log 2 (N + n + 1) + 56)` pointer-machine instructions, including halt.
The general `executes_compile` theorem preserves the complete represented source state and
bounds time by `n * (294 * Nat.log 2 (M + 1) + 56)`, where `M` is the final dictionary size.

The target has seven pointer registers, `r + 4` scalar registers for a source with `r`
registers, and records with three links (left, right, parent) and three scalar fields
(key, height, value). The verified
[AVL dictionary](../../CslibFrontier/DataStructure/AVLTree/PointerMachine/Dictionary.lean)
reads an absent address as zero and inserts or overwrites on a store. It retains entries
written back to zero, so `M` counts retained addresses, rather than just nonzero memory cells.
A source step allocates at most one record. Memory reads, writes, rotations, allocation,
control flow and scalar instructions are all charged.

The explicit `inputState` encoding builds a valid AVL dictionary for the length cell and
input cells, using exactly `N + 1` records. Input encoding is outside the execution charge,
as in the source `Data.init` convention. It is constructed and proved correct, rather than
supplied as an assumed dictionary implementation. The
[compiler client](../../CslibFrontierTests/WordRAMPointerMachine.lean) checks memory updates,
missing addresses, register aliasing, backward loops, and the general simulation theorem.

The scalar model `model w` supplies the standard word-RAM arithmetic, constants and width
operation, together with the AVL height operations and comparisons. Simulated addresses are
natural-number scalars on which source arithmetic is allowed. Resolving an address requires
traversing physical heap pointers; the scalar operations cannot inspect or construct those
pointers. This result does not claim simulation by an atom-only model, nor fault equivalence
or randomized execution. Source `rand` instructions fault in the deterministic semantics and
cannot occur on the successful runs covered by the theorem.

## Known Limitations

The source survey does not establish a uniform finite encoding of exact real inputs, nor a native certificate for every algebraic interpretation. It does not identify the natural RAM, generic RAM and upstream typed-bank RAM by naming alone. An upstream typed-bank RAM proposal (CSLib #1158) was closed unmerged on 2026-11-02; no local semantic identification with that design was found in the inspected sources.

[complexitylib]: ../sources.md#complexitylib
[cookreckhow73]: ../sources.md#cookreckhow73
[erickson24]: ../sources.md#erickson24
