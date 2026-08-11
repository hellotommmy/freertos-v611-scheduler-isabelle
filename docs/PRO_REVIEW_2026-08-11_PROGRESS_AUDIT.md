# External Pro review: universal-progress audit (2026-08-11)

This note preserves the actionable conclusions of the dedicated Pro review at:

<https://chatgpt.com/c/6a7a7409-0400-83ee-b1d7-3751b060a4c5>

The review is advisory. It is not Isabelle evidence and cannot turn an
unregistered theory or a red session into a checked theorem.

## Completion accounting

- The strongest honest headline is **conditional boundary-to-boundary
  sequential correctness**, not complete scheduler correctness.
- A coarse, predeclared 20-gate ledger can provisionally be counted as
  A 6/8 + B 2/5 + C 0/4 + D 1/3 = **9/20 = 45%**.
- That 45% is not yet fully third-party reproducible because A1--A8 are not
  individually named in the repository report. They should be enumerated
  before this denominator is treated as stable.
- `xTaskGetTickCount_refines` is a root-local functional result under its
  small tick/depth/mask relation. It does not yet supply the latest full
  cursor-general common scheduler frame. Counting it in B=2/5 must carry
  that qualification.
- For the stricter common-boundary acceptance target, the repository evidence
  supports an audit range of **35--40%**. Reusable proof infrastructure is
  reasonably described as **45--50%**. Neither number is a kernel output.

## Claim language

Safe wording:

- cursor-general, managed-domain generated `vTaskIncrementTick'` is checked at
  an already-established settled/unmasked public boundary;
- all arithmetic classes are distinguished, including a no-success result for
  literal signed overflow;
- arbitrary finite repeated tick calls are checked under a caller-supplied
  stable relation and per-step arithmetic enabledness;
- arbitrary finite due-prefix generated while/finally is checked, including
  empty and future-exception exits.

Unsafe wording:

- full FreeRTOS scheduler verification;
- all five roots for all legal inputs;
- arbitrary mixed scheduler traces;
- concurrency linearisation derived from sequential `runs_to`;
- boot/allocator reachability;
- calling the public relation fully "ghost-free". The precise phrase is
  **caller-facing witness hiding** or **no explicit witness parameter**.

## Load-bearing open counterexamples

1. Resume replay runs the tick at proof-port critical depth/mask `1/1`, while
   the checked public tick boundary uses `0/0`.
2. Current-state arithmetic definedness is not replay-horizon safety. With
   tick `MAX_WORD-1`, signed-max overflow, and missed debt 2, the first replay
   succeeds and the second wrap has no successful successor.
3. A replay body must pin scheduler suspend depth to zero; otherwise the tick
   increments missed debt and the following decrement cancels it.
4. Managed tasks may strictly contain runnable live tasks because termination
   retains retired tasks. A live-only Resume gate is not universal.
5. The proof-port yield counter is modular; an abstract unbounded `Suc` cannot
   re-establish the common snapshot at `MAX_WORD`.

## Recommended eight-rung continuation

1. Check the two-field overlay algebra and exact `rel_spec` run-image rules in
   the small probe session.
2. Prove the unlocked generated tick source self-bisimulation under that
   overlay, compositionally.
3. Transfer the checked public tick theorem to the protected `1/1` cutpoint.
4. Prove one missed-replay body in source order: tick, then debt decrement.
5. Prove horizon-safe replay success plus first-unsafe no-success.
6. Strengthen the pending drain/loop continuation to preserve exact proof-port
   fields.
7. Generalise the Resume gate to the managed/termination/external domain.
8. Use a modular yield relation and close the outer `xTaskResumeAll` exit back
   to the settled public boundary.

Each rung should have its own child session, `quick_and_dirty=false`, one
Isabelle lane, and a measured bounded timeout. On timeout, bisect the first
unfinished command instead of increasing the whole scheduler timeout.
