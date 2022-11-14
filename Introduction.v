(******************************************************************************)
(**
  This section presents some notes on the formalization of Movec's monitoring
  algorithm for the dynamic analysis of memory safety, using the Coq proof assistant.
  Without obscuring the formalization with the size and complexity of the full
  implementation, we will focus on the key components of Movec's mechanisms,
  say metadata propagation and memory-safety checking. *)

(******************************************************************************)
(** *                 The overall structure                                   *)
(******************************************************************************)
(**
  The presentation proceeds in three steps.

  First, we formalize a fragment of C #<a href="Top.Types.html">#types#</a>#,
  including atomic types and structure types which permit recursive data
  structures.

  We formalize a #<a href="Top.Envs.html">#memory model#</a># that includes
  global variables, heap and stack, as well as #<a href="Top.Envs.html">#
  well-formedness predicates#</a># on environment that capture invariants.

  We define a fragment of C #<a href="Top.Syntax.html">#syntax#</a># that
  covers almost all of Movec's features, including the dereference operator *,
  the member operator ->, the sizeof operator, the address-of operator &,
  the type cast operator, pointer arithmetics, malloc, free, assignments,
  and a simple form of function call that has no arguments or results,
  but does allow stack pointers to escape via the heap.

  With these utilities, we develop a #<a href="Top.CSemantics.html">#
  non-standard operational semantics#</a># for (simplified, straight-line,
  and single-threaded) C programs that tracks information about which
  memory addresses have been allocated. Crucially, this semantics is
  #<i>#partial#</i># - it is undefined whenever a bad C program would cause
  a memory-safety violation; for programs without memory errors, this
  semantics agrees with C.

  Second, we #<a href="Top.ISemantics.html">#augment the operational semantics#</a>#
  so that it both propagates the metadata and performs memory-safety assertions,
  aborting the program upon assertion failure, with augmented memory model and
  runtime primitives that manipulate memory and metadata. This step abstractly
  models the results of memory safety instrumentation of the C program.

  We establish the #<a href="Top.Axioms.html">#axiomatization#</a># of the C runtime
  primitives for accessing memory: read, write, malloc, free, function frame
  allocation and deallocation.

  Finally, based on a #<a href="Top.LibBehavior.html">#library of proved lemmas on
  behavior#</a>#, we prove #<a href="Top.BehavSim.html">#backward behavior
  simulation#</a># that if an instrumented program terminates successfully, the
  original C program will not cause any memory-safety violation.

  In conclusion,
  the instrumented program will either terminate without any memory violation,
  cause a system error (exhausting memory, deallocating an invalid memory, etc),
  or abort - it will never get stuck trying to access memory. *)

(******************************************************************************)
(** *                 Meta-variable names                                     *)
(******************************************************************************)
(**
  In the proof, we use the following meta-variable names:
#
<table border="1" align="center">
<caption>Meta-variable Names</caption>
<tr>
<th>Meta-variables</th>
<th>Usage</th>
</tr>
<tr>
  <td>id, n</td>
  <td>Identifiers, Named Struct Types</td>
</tr>
<tr>
  <td>a</td>
  <td>Atomic Types</td>
</tr>
<tr>
  <td>s</td>
  <td>Anonymous Struct Types</td>
</tr>
<tr>
  <td>r</td>
  <td>Referent Types</td>
</tr>
<tr>
  <td>l</td>
  <td>Locations</td>
</tr>
<tr>
  <td>v</td>
  <td>Values</td>
</tr>
<tr>
  <td>b</td>
  <td>Bases</td>
</tr>
<tr>
  <td>e</td>
  <td>Bounds</td>
</tr>
<tr>
  <td>sa</td>
  <td>Status Node Addresses</td>
</tr>
<tr>
  <td>p, pmd</td>
  <td>Pointer Metadata</td>
</tr>
<tr>
  <td>f</td>
  <td>Functions</td>
</tr>
<tr>
  <td>v</td>
  <td>Variables</td>
</tr>
<tr>
  <td>M</td>
  <td>Memory</td>
</tr>
<tr>
  <td>G</td>
  <td>Global Variables</td>
</tr>
<tr>
  <td>AMB</td>
  <td>Allocated Memory Blocks</td>
</tr>
<tr>
  <td>fr</td>
  <td>Frames</td>
</tr>
<tr>
  <td>K</td>
  <td>Stack Variables</td>
</tr>
<tr>
  <td>PT</td>
  <td>Pointer Metadata Tables</td>
</tr>
<tr>
  <td>ST</td>
  <td>Status Node Tables</td>
</tr>
<tr>
  <td>E</td>
  <td>Environments</td>
</tr>
<tr>
  <td>R</td>
  <td>Evaluation Results</td>
</tr>
<tr>
  <td>lhs</td>
  <td>LHS expressions</td>
</tr>
<tr>
  <td>rhs</td>
  <td>RHS expressions</td>
</tr>
<tr>
  <td>c</td>
  <td>Commands</td>
</tr>
</table>
#
*)
