# Resume depth-zero machine-path classification — 2026-08-12

Baseline: `7f61877` on `agent/universal-scheduler-refinement`.

## Checked scope

This child classifies the invalid suspension-depth-zero call to the real
translated `Scheduler_V611_Delay_Translation.xTaskResumeAll'`.  It does not
pretend that this input satisfies the abstract Resume API contract.

At concrete suspension word zero, the generated unsigned decrement wraps to
`0xFFFFFFFF`.  The decremented word is nonzero, so the function takes the
early-return branch, exits the critical section, and returns `Result 0`
without reading pending tasks, missed ticks, the current task, a TCB, a list
root, or the heap.  The exact source theorem frames the complete globals and
records the wrapped suspension word.

In contrast, `ResumeRel` requires a positive pre-state suspension depth, and
nat subtraction maps abstract zero to zero.  The candidate post therefore
cannot satisfy the cursor-general modular endpoint: its concrete suspension
word has `unat 0xFFFFFFFF`, while its truncated abstract suspension depth is
zero.  The public theorem packages these facts under only the initial modular
endpoint and `sa_suspend_depth a = 0`.

This is a domain-violation/machine-behaviour theorem.  The actual source path
is successful; it is not a no-run, exception, rollback, or divergence result.
It deliberately carries no outermost current-safety, replay-horizon,
pending-ring, task-count, no-wrap, cursor-None, `managed = sa_live`,
termination-empty, desired-post, or legacy pending-gate premise.

## Theorem-object audit

| theorem | premises | hidden hypotheses |
| --- | ---: | ---: |
| `scheduler_xTaskResumeAll_zero_underflow_exact` | 3 | 0 |
| `ResumeRel_zero_depth_invalid` | 1 | 0 |
| `CursorGeneralStrongSchedulerModularEndpointRel_zero_underflow_impossible` | 2 | 0 |
| `CursorGeneralStrongSchedulerModularEndpointRel_generated_xTaskResumeAll_depth_zero_invalid` | 2 | 0 |

The embedded ML audit rejects any changed premise count or hidden hypothesis.

## Checker topology and chronology

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Outer_Loop_Depth_Zero` is a
one-theory child of the frozen nested session, with `document=false`,
`quick_and_dirty=false`, `parallel_proofs=0`, and `timeout=120`.  The project
wrapper discovers the top and generated-vcg ROOTs, uses
`-o quick_and_dirty=false`, and runs with `-j 1`.

Runs 01 and 02 ended at their first proof-plumbing error.  Isabelle did not
automatically turn `unat w = 0` into `w = 0`, first for the pre-state word and
then for the explicit post-state `MAX_WORD` contradiction.  Both repairs use
the existing `unat_eq_zero` fact; no theorem statement or premise changed.

| run | elapsed | result |
| --- | ---: | --- |
| `01-underflow-classification` | 682.132 s | red; pre-state `unat w = 0` bridge missing |
| `02-unat-zero-bridge` | 661.214 s | red; post `MAX_WORD = 0` contradiction not staged |
| `03-explicit-maxword-contradiction` | 661.706 s | green; all four objects and ML ledgers passed |

The promoted run is:

- run: `20260812Tresume-managed-outer-loop-depth-zero-03-explicit-maxword-contradiction`
- `exit_code=0`
- `timed_out=false`
- `quick_and_dirty=false`
- `elapsed_seconds=661.706`
- leaf theory: 5 s

Evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `6DA031B92746D065C9A5C48AD26AECA61757EAACFA531C848E57003241ACC1D8` |
| `command.txt` | `29E09851EF767D4B90FCE733175E5BE673C6B85D1BAC321D04791D95EFC09B16` |
| `status.txt` | `8536E799E1FCB43A93A35D137604494B6021359D6F1BF9DA41C1DBA26040AFC9` |
| `stdout.log` | `139B6AC606300F14DA0984F247806AE161C4F826FACC1893DD5BF957787628D8` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

The frozen-layout ELF, frozen-layout ledger, and generated address
configuration remained respectively
`DC830E50513384D712E0D1C68CB198EA656365F673D021C452D7D7EBD45C045A`,
`CA288A4CD2344BE979ADFA9DBF0298C6715F196D64AE472D173304289C4F2C02`,
and `27F74768E1DB1C3F8DBFCFC85371075192BB7D2544ED324DC81B65A9A2911712`.

## Exact next boundary

The legal nested and invalid zero-depth machine branches are now explicit.
The next proof boundary is the modular transport that relates the normalized
outermost safe result back to the original unbounded abstract yield count and
then packages the branch-complete public Resume theorem.  Delay/tick/mixed
traces, sequential/concurrent contracts, and the final whole-repository check
remain later obligations.
