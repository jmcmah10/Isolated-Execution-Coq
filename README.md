# Isolated-Execution-Coq
Coq files for isolated execution paper

# FILES
# RuntimeDefinitions.v
Coq definitions from the "Runtime Definitions" diagram (top of file), as well as lemmas and functions that are commonly used through the later files (bottom of file).

# AppendixC.v
Functions for Auxiliary "Definitions Related to Single-Level Physical Cache Units" (currently section A.4). Contains cachelet-related functions (allocation, deallocation, read, write, invalidation, and update).

# AppendixD.v
Function definitions for "Definitions and Auxiliary Functions of the Cache Replacement Logic" (currently section A.5). There are only four functions here:
- equal_enclave_IDs: checks if two enclaves are equal, which happens when both are active with the same ID or both are inactive
- contains_way_ID: in paper, checks if PLRU-tree holds a way ID
- update: in paper, updates PLRU tree after read or write (implemention later in paper)
- replace: in paper, finds which enclave to evict from a PLRU tree

# AppendixE.v
Functions for "Definitions and Auxiliary Functions of the Enclave" (currently section A.6). Contains enclave-related functions (creation, update, and elimination).

# AppendixF.v
Functions for "Auxiliary Defintions of Main Memory" (currently section A.7). Contains functions to reinitialize memory.

# MLCOperations.v
Definitions and functions for the mutli-level cache, separated into two parts:

Cache Hierarchy Tree:
In the paper, the cache hierarchy is represented as a function that operates on this tree.
In coq, the cache hierarchy is represented as a mapping from a node on the tree (the root node, a core, or a cache unit) to the path to the root node.
For example, given a single core cpu with an L1 and L2, we would get some tree structure that looks like:
core -> l1 -> l2 -> root
then, the mapping in coq would look like:
core: [ core, l1, l2, root ]
l1: [ l1, l2, root ]
l2: [ l2, root ]
root: [ root ]

Multi-Level Cache Operations:
Definitions for functions in the paper named MLC Read (currently fig 6), MLC Allocation (currently fig 7), MLC Write (currently fig 17), and MLC Deallocation (currently fig 18).

# Semantics.v
Definition for operational semantics of MLC and TEE. This include two groups of semantics, multi-process semantics and single process semantics.
The multi-process semantics are [MULTI] and [CONTEXTSWITCH], as defined in the paper.
The single process semantics are evaluated during the [MULTI] semantic, as defined in the paper.

This section also contains a definition of "disjoint enclave states", which claims that given any two different enclave states, their domains must be disjoint. This definitions is used in the [MULTI] semantic, and is a necessary condition for well-formedness.

# WellFormed.v
The first part contains "helper lemmas", which is a list of lemmas used in later proofs.

The second part contains definition and preservation proofs of the first two conditions of well-formedness. This includes F ⊆ dom(C) (defined as well-formed 1), ran(V(e)) ⊆ dom(C) for any e ∈ dom(V) (defined as well-formed 2).

Well-formed 1 and well-formed 2 preservation are closely linked due to the defintion of the [CREATE] and [DESTROY] semantics.
The [CREATE] semantic removes a cachelet index from F and adds it to V, and the [DESTROY] semantic removes a cachelet index from V and adds it to F.
Because of this, both well-formed 1 and well-formed 2 are required as initial conditions in well-formed 1 preservation and well-formed 2 preservation.
The two other semantics with non-trivial proofs are [LOAD] and [STORE].

To prove preservation over the semantics, the "inversion" tactic is used, first on the multi-level semantics, indicated by "===>", and then on the single level semantics, indicated by "-->>".
Within each of these cases, an inductive proof is used to show preservation through the MLC functions, and within each MLC function, an inductive proof is used to show preservation through the single-level cachelet function.

# WellFormedEnclaveState.v
Includes lemmas related to the enclave creation and enclave elimination functions.
Also includes a definition for the property "active enclave contained", which states that given any enclave state <e, E>, e ∈ dom(E).
There is also a preservation proof for this property.

# WellFormed2.v
Contains definitions and preservation proofs of four well-formedness conditions. This includes F ∩ ran(V(e)) = ∅ for any e ∈ dom(V) (defined as well-formed 3), e = ⊥ or e ∈ dom(E) for any p such that π(p) = ⟨ε; l⟩, and ε = ⟨e; E⟩ (defined as well-formed 4), there exists ⟨F′;V ′;C′; R′⟩ ∈ ran(κ) such that e ∈ dom(V ′) for any p such that π(p) = ⟨ε; l⟩, and ε = ⟨e; E⟩ (defined as well-formed 5), and μ(l0) = ι for some ι and μ(l) = n1, . . . , μ(l + k − 1) = nk for some n1, . . . , nk for any p such that π(p) = ⟨ε; l0⟩, and ε = ⟨e; E⟩ and ⟨l; k⟩ ∈ ran(E) (defined as well-formed 6).

For well-formed 3, there are three extra conditions that need to be explicitly defined:
- F must have no duplicates
- forall e, ran(V(e)) has no duplicates
- forall e e' such that e != e', ran(V(e)) and ran(V(e')) are disjoint
This causes the proofs to have a few more conditions than well-formed 1 and well-formed 2, but the overall structure and reasoning of the proof is about the same.

In well-formed 4 and well-formed 5, both the multi-level cache and processes are involved. Because all of the single-process semantics effect the processes, all of the proofs require some level of analysis. The logic for [LOAD], and [STORE] are the same as well-formed 1 and well-formed 2. On the other hand, [CREATE] and [DESTROY] require similar logic for the multi-level cache, but also involves some extra cases for created and destroyed enclaves (hence the addition of wf4_enclave_creation, etc). [ENTER] and [EXIT] require only analyzing the enclave state in the process, as both semantics only modify the active enclave. The [ENTER] semantic in particular is where the "active enclave contained" property must be used.

Well-formed 6 is currently incomplete (and so far very difficult to prove O_O) 

# WellFormed3.v
Contains definitions and preservation proofs of three well-formedness conditions. The seventh and eighth conditions are broken into two parts, as they are "if and only if"s in the paper, their definitions have different quantifiers in each direction. Because of this, each well-formed condition is split into two.
These conditions are: forall w s, (w, s) ∈ C -> s ∈ R (defined as well-formed 7-1), forall s, s ∈ R -> exists w, (w, s) ∈ C (defined as well-formed 7-2), forall w s, (w, s) ∈ C -> exists y T, w ≺ T and T ∈ ran(R) (defined as well-formed 8-1), and forall w, exists y T s.t. w ≺ T and T ∈ ran(R) -> exists s, (w, s) ∈ C.
All the well-formed 7 and well-formed 8 conditions are related to the multi-level cache, so much like well-formed 1, 2, and 3, the only semantics with non-trival proofs are [CREATE], [DESTROY], [LOAD], and [STORE].

The last well-formedness condition is e ⊏ T and T ∈ ran(R) -> e ∈ dom(V ) ∪ {⊥}, defined as well-formed 9. (still working on this one as well).

# Note on induction in Coq
In coq, variables can be more or less general in induction proofs depending on which variables are defined in "intros".

Here is a simple example of this in action:

******************************************************
Theorem add_assoc_intros : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem add_assoc_no_intros : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - intros. simpl. rewrite (IHn' m p). reflexivity.
Qed.
******************************************************

In the first proof, all variables are introduced at the beginning, so when the "rewrite" tactic is used, no more variables need to be defined.
In the second proof, only the variable "n" is defined, so when the "rewrite" tactic is used, the other variables in the proposition must be defined.
This is used extensively in the Coq proofs, as some proofs cannot be completed without generalizing some variables.