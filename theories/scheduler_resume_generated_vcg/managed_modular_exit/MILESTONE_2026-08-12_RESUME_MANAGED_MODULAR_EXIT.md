# Resume managed modular exit — 2026-08-12

Baseline: `ab6c51f` on `agent/universal-scheduler-refinement`.

## Checked scope

This exclusive child proves the exact generated exit-critical leaf and exports
the public modular endpoint reached from a protected modular tick-entry state.
Its concrete transformer is

`resume_managed_exit_critical_state c = scheduler_port_overlay 0 0 c`.

The child checks:

- the generated `eal6_port_exit_critical'` source at exact critical depth `1`,
  returning `Result ()` and the exact transformed concrete state;
- a pure bridge from
  `CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel D 1 irq_mask`
  to `CursorGeneralStrongSchedulerModularEndpointRel` at that state, for an
  arbitrary incoming interrupt mask; and
- the generated source capstone combining the exact leaf with that bridge.

The bridge unpacks the protected relation at
`normalize_yield_count_abs a`, recovers its public shadow, uses the checked
public-entry/endpoint boundary, and proves that one exit from depth `1`
recovers the shadow at proof-port depth and interrupt mask `0`.  The original
unbounded abstract yield count is retained through the separate
`yield_count_mod_rel`; the proof does not route through an exact endpoint
adapter that would lose that count.

Depth `1` is load-bearing.  At depth `2`, one generated exit leaves depth `1`
and preserves the incoming interrupt mask, so the public endpoint conclusion
would be false.  No premise fixing the incoming interrupt mask is needed at
depth `1`, because the generated source reaches depth `0` and writes the mask
to `0`.  No no-wrap premise, legacy managed gate, managed/live equality, or
cursor premise is used.

## Theorem-object audit

| theorem | premises | hidden hypotheses |
| --- | ---: | ---: |
| `resume_managed_eal6_port_exit_critical_exact` | 1 | 0 |
| `CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_exit_criticalD` | 1 | 0 |
| `CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_generated_exit_critical` | 1 | 0 |

The embedded ML ledger checks exactly three `1/0` theorem objects.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Modular_Exit` has sole parent
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Modular_Yield`, one theory,
`document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=120`.  The repository wrapper used a 600-second lifecycle budget and
both repository ROOT discovery directories.

The bounded first-error chronology was:

| run | exit | elapsed | first result |
| --- | ---: | ---: | --- |
| `20260812Tresume-managed-modular-exit-01-public-endpoint` | 1 | 278.919 s | the exact source leaf exposed its generated VCG branch obligations |
| `20260812Tresume-managed-modular-exit-02-depth-all-branches` | 142 | 372.501 s | broad `simp_all` timed out inside the session after VCG completed |
| `20260812Tresume-managed-modular-exit-03-explicit-depth-branches` | 142 | 379.523 s | a focused broad `simp` still traversed the record goal and timed out |
| `20260812Tresume-managed-modular-exit-04-scalar-contradictions` | 1 | 264.628 s | the first branch was the concrete record-update branch, not a contradiction |
| `20260812Tresume-managed-modular-exit-05-pure-depth-contradictions` | 1 | 266.344 s | premise indexing attempted to use a record equality as a scalar rule |
| `20260812Tresume-managed-modular-exit-06-record-main-branch` | 1 | 260.023 s | the main record branch passed; the next scalar branch needed its local context |
| `20260812Tresume-managed-modular-exit-07-context-contradictions` | 1 | 264.587 s | the third branch's local negation had not been introduced explicitly |
| `20260812Tresume-managed-modular-exit-08-third-premises` | 1 | 258.641 s | generic contradiction did not consume the named object-level negation |
| `20260812Tresume-managed-modular-exit-09-direct-third-negation` | 1 | 304.320 s | object-level `\<not> P` was incorrectly composed as a meta-premise with `OF` |
| `20260812Tresume-managed-modular-exit-10-propositional-third-branch` | 1 | 291.782 s | three focused branches closed; the fourth unreachable VCG path surfaced at `done` |
| `20260812Tresume-managed-modular-exit-11-fourth-depth-contradiction` | 0 | 263.828 s | green; leaf reported 4 s |

Runs 02 and 03 reached the session command timeout (`exit=142`) while the
outer wrapper itself recorded `timed_out=false`; every other run was also an
outer non-timeout run.  Every run used `quick_and_dirty=false`.  Repairs were
limited to deterministic proof plumbing in the exact source leaf; all three
theorem statements and premise ledgers stayed unchanged.  Run 11 is the
promoted final evidence.

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `EF269414ACDF0D5554617D655B34687690BC943DC1264709DD2B7894079EA0BB` |
| `command.txt` | `BA26BBF96F486116AC638D86EA09031FCC98B29444298A247723BCA854FFB0B3` |
| `status.txt` | `3ECCCBB24140E605E676B5AF3AE2C3AD25A3027926A86E1CFC29FB64D9908D63` |
| `stdout.log` | `7EC7AD07872E02937596DEF9220D13CFD0C5ECD37504B196C648CCEE1AA44B58` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

Frozen-layout evidence recorded by the final status:

- ELF: `DC830E50513384D712E0D1C68CB198EA656365F673D021C452D7D7EBD45C045A`
- ledger: `CA288A4CD2344BE979ADFA9DBF0298C6715F196D64AE472D173304289C4F2C02`
- generated address configuration:
  `27F74768E1DB1C3F8DBFCFC85371075192BB7D2544ED324DC81B65A9A2911712`

## Exact remaining boundary

This child deliberately stops at the checked public modular endpoint after
the exit-critical primitive.  It does not start the outer continuation or
compose the whole generated resume operation.
