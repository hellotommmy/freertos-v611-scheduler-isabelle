# Resume managed modular yield — 2026-08-12

Baseline: `185712a` on `agent/universal-scheduler-refinement`.

## Checked scope

This exclusive child proves the proof-port yield primitive and the complete
generated yield branch over the protected modular tick-entry relation.  The
primitive increments the concrete 32-bit yield counter while the abstract
counter remains unbounded, including at wrap.  The branch retains the literal
generated guard

`y = 1 \<or> xMissedYield_' s = 1`

for arbitrary `int` `y`; it does not replace that guard by `y \<noteq> 0`.

The child checks:

- the concrete yield-count selector and proof-port overlay frame;
- core, cursor-canonicalization, cursor-general-core, and current-relation
  framing for the paired yield-count step;
- the exact `eal6_port_yield'` source leaf and exact `p2_yield_state`;
- cursor-general Snapshot and protected-entry reconstruction after increment;
- the staged normalized request-yield equality under
  `yield_count_mod_rel`;
- modular protected-entry preservation through `request_yield`;
- concrete observation of the protected missed-yield bit; and
- a one-premise, branch-complete source theorem covering all four combinations
  of the literal local guard and the abstract missed-yield flag.

On the true branch the exact source order is clear missed-yield, call the yield
primitive, then return `1`.  Its concrete post is
`p2_yield_state (resume_clear_missed_yield_state c)` and its abstract post is
`request_yield (a\<lparr>sa_missed_yield := False\<rparr>)`.  On the false branch
the source returns `0` and preserves both states.  The exported `YieldAbs` and
modular protected-entry post agree with both branches.

The proof does not assert
`normalize_yield_count_abs (request_yield a) =
 request_yield (normalize_yield_count_abs a)`, which is false at the maximum
32-bit word.  Instead, under the modular counter premise it first rebuilds the
exact normalized Snapshot with count `unat (w + 1)` and only then identifies
that state with `normalize_yield_count_abs (request_yield a)`.  No no-wrap,
legacy managed gate, managed/live equality, or runtime-word/proof-ghost
identification is used.

## Theorem-object audit

| theorem | premises | hidden hypotheses |
| --- | ---: | ---: |
| `p2_yield_state_yield_count` | 0 | 0 |
| `p2_yield_state_port_overlay` | 0 | 0 |
| `core_wf_yield_count_update` | 0 | 0 |
| `canonicalize_scheduler_cursors_yield_count_update` | 0 | 0 |
| `cursor_general_core_wf_yield_count_update` | 0 | 0 |
| `scheduler_current_rel_p2_yield_state` | 0 | 0 |
| `resume_managed_eal6_port_yield_exact` | 0 | 0 |
| `CursorGeneralStrongSchedulerSnapshotRel_p2_yield_stateI` | 1 | 0 |
| `CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_p2_yield_stateI` | 1 | 0 |
| `normalize_yield_count_abs_request_yield_step` | 1 | 0 |
| `CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_p2_yield_stateI` | 1 | 0 |
| `CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_generated_yield` | 1 | 0 |
| `CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_missed_yieldD` | 1 | 0 |
| `CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_generated_yield_branch` | 1 | 0 |

The embedded ML ledger checks exactly seven `0/0` theorem objects followed by
seven `1/0` theorem objects.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Modular_Yield` has sole parent
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Modular_Clear`, one theory,
`document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=120`.  The repository wrapper used a 600-second lifecycle budget and
Isabelle options `-o quick_and_dirty=false -j 1` with both repository ROOT
discovery directories.

The bounded discovery chronology was:

| run | exit | elapsed | first result |
| --- | ---: | ---: | --- |
| `20260812Tresume-managed-modular-yield-01-staged-wrap` | 1 | 274.109 s | reserved local name `next` caused an outer-syntax error |
| `20260812Tresume-managed-modular-yield-02-counter-name` | 0 | 258.584 s | primitive modular-yield ladder green; branch theorem not yet present |
| `20260812Tresume-managed-modular-yield-03-branch-complete` | 1 | 262.786 s | true-block simplification had already closed the return continuation |
| `20260812Tresume-managed-modular-yield-04-bind-closure` | 1 | 259.005 s | false post needed staged requested/caller/final normalization |
| `20260812Tresume-managed-modular-yield-05-false-normalization` | 1 | 259.145 s | unfolding `YieldAbs` reopened conditional false-post goals |
| `20260812Tresume-managed-modular-yield-06-yieldabs-false` | 1 | 258.106 s | broad terminal simplification retained the same conditional goals |
| `20260812Tresume-managed-modular-yield-07-explicit-false-entry` | 1 | 258.870 s | explicit simplification exposed three distinct VCG goals |
| `20260812Tresume-managed-modular-yield-08-explicit-false-conjuncts` | 1 | 261.133 s | VCG had already split the post, so `conjI` was inapplicable |
| `20260812Tresume-managed-modular-yield-09-three-false-goals` | 0 | 259.091 s | green; leaf reported 8 s |

Every recorded run was non-timeout and `quick_and_dirty=false`.  Each red was
handled at its first failure with a proof-plumbing-only repair; the theorem
statements and premise ledgers stayed fixed after the branch-complete interface
was introduced.  Run 09 is the promoted final evidence.

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `5EDCCDDC6EC781EB43D2CFE0454F4EE675EB685A4CECC84088C11A0D4209D484` |
| `command.txt` | `9366BC52141643AA6DCA1F0B0DAE9F3FB5E2DE306F10B24BFE9EEF248E3341C4` |
| `status.txt` | `4F38DE0D7E403DCB6C2ED36B97E7E1437FB19E7D943798D59DAA78C403F11A05` |
| `stdout.log` | `8176ABDAE9BC3CFB258782A270CBF5CBBC533FC674F769817AC960E4671CB101` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

Frozen-layout evidence recorded by the final status:

- ELF: `DC830E50513384D712E0D1C68CB198EA656365F673D021C452D7D7EBD45C045A`
- ledger: `CA288A4CD2344BE979ADFA9DBF0298C6715F196D64AE472D173304289C4F2C02`
- generated address configuration:
  `27F74768E1DB1C3F8DBFCFC85371075192BB7D2544ED324DC81B65A9A2911712`

## Exact remaining boundary

This child proves the complete local guarded-yield branch, but not yet the
whole generated resume operation.  The next thin rung should compose the
checked managed-loop/replay result with this branch and the exit-critical
source step, then expose the public modular endpoint.  It must retain the
literal equality test `y = 1`, the separate missed-yield flag semantics, and
the modular counter relation across wrap.
