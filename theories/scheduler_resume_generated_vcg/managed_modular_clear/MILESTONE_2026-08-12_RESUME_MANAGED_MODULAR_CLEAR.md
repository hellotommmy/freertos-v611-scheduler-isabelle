# Resume managed modular clear — 2026-08-12

Baseline: `6f66fc7` on `agent/universal-scheduler-refinement`.

## Checked scope

This exclusive child proves the literal generated-source update
`xMissedYield := 0` while pairing it with the abstract update
`sa_missed_yield := False`.  It preserves the protected modular tick-entry
relation and the separate modular yield-count observation, including at word
wrap.

The child introduces the transparent concrete-state name
`resume_clear_missed_yield_state` and checks:

- normalization commutation with the distinct abstract missed-yield field;
- concrete yield-count framing and proof-port overlay commutation;
- core, cursor-canonicalization, cursor-general-core, and current-relation
  framing;
- exact cursor-general Snapshot preservation with the same family witnesses;
- protected public-shadow reconstruction;
- protected modular-entry preservation; and
- the exact `modify (xMissedYield_'_update (\<lambda>_. 0))` source step,
  including `Result ()` and the literal updated state.

The source theorem does not call the yield primitive, encode the runtime local
word in a proof ghost, add a no-wrap premise, use the legacy managed gate, or
leave the abstract missed-yield flag unchanged.  The modular counter is framed
because neither the concrete nor abstract yield count changes.

## Theorem-object audit

| theorem | premises | hidden hypotheses |
| --- | ---: | ---: |
| `normalize_yield_count_abs_missed_yield_update` | 0 | 0 |
| `resume_clear_missed_yield_state_yield_count` | 0 | 0 |
| `resume_clear_missed_yield_state_port_overlay` | 0 | 0 |
| `core_wf_missed_yield_update` | 0 | 0 |
| `canonicalize_scheduler_cursors_missed_yield_update` | 0 | 0 |
| `cursor_general_core_wf_missed_yield_update` | 0 | 0 |
| `scheduler_current_rel_clear_missed_yield` | 0 | 0 |
| `CursorGeneralStrongSchedulerSnapshotRel_clear_missed_yieldI` | 1 | 0 |
| `CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_clear_missed_yieldI` | 1 | 0 |
| `CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_clear_missed_yieldI` | 1 | 0 |
| `CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_generated_clear_missed_yield` | 1 | 0 |

The embedded ML ledger checks exactly seven `0/0` theorem objects followed by
four `1/0` theorem objects.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Modular_Clear` has sole parent
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Modular_Endpoint`, one theory,
`document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=120`.  The repository wrapper used a 600-second lifecycle budget and
Isabelle options `-o quick_and_dirty=false -j 1`.

The bounded discovery chronology was:

| run | exit | elapsed | first result |
| --- | ---: | ---: | --- |
| `20260812Tresume-managed-modular-clear-01-paired-clear` | 1 | 264.260 s | Snapshot current-relation frame needed staged rewriting |
| `20260812Tresume-managed-modular-clear-02-staged-current-frame` | 1 | 260.728 s | thin source wrapper needed an explicit `show` |
| `20260812Tresume-managed-modular-clear-03-explicit-show` | 1 | 258.675 s | literal updater and named clear state did not simplify as a chained fact |
| `20260812Tresume-managed-modular-clear-04-definitional-state` | 1 | 255.414 s | rejected non-Isar `change` repair; no theorem change |
| `20260812Tresume-managed-modular-clear-05-unfolded-preservation-rule` | 1 | 256.031 s | VCG exposed separate exact-state and relation goals |
| `20260812Tresume-managed-modular-clear-06-explicit-vcg-goals` | 0 | 254.094 s | green; leaf reported 7 s |

Every recorded run was non-timeout and `quick_and_dirty=false`.  Each red was
handled at its first failure with a proof-plumbing-only repair; all statements
and premise ledgers remained fixed.

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `80495AEF84054FE088D127A289E05A55FD998366353D816818E339BB8C773A43` |
| `command.txt` | `0E5770A2A37A699A8F7205A6237177376FAE4342C8EB62144C7448828BB9F5CE` |
| `status.txt` | `51C52865F701BDD2C8276E2CCBBBB2E1C078CC39E30F33D4F3D76D75789E164E` |
| `stdout.log` | `0E382A7EEE70ACE4409378A0109715803B2E35DB3F3D125D2F5364BE8686D3F9` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

Frozen-layout evidence recorded by the final status:

- ELF: `DC830E50513384D712E0D1C68CB198EA656365F673D021C452D7D7EBD45C045A`
- ledger: `CA288A4CD2344BE979ADFA9DBF0298C6715F196D64AE472D173304289C4F2C02`
- generated address configuration:
  `27F74768E1DB1C3F8DBFCFC85371075192BB7D2544ED324DC81B65A9A2911712`

## Exact remaining boundary

The next child handles the literal guarded yield branch.  It must rebuild the
normalized post Snapshot directly and use `yield_count_mod_rel_request`; it
must not assert commutation of yield-count normalization with
`request_yield`, which is false at the maximum 32-bit word.  The source guard
remains the literal local test `y = 1`.
