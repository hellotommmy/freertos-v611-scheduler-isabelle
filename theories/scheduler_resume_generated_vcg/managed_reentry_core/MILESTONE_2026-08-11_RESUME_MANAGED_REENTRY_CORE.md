# Resume managed re-entry core — 2026-08-11

Baseline: `111e586df760f5cce3dcb693554da6dc6ebd316e` on
`agent/universal-scheduler-refinement`.

## Checked scope

This exclusive child proves that one abstract pending-resume step preserves the
cursor-general scheduler core.  The proof uses `canonicalize_scheduler_cursors`
only as a proof shadow: pending and suspended removals commute with the
canonical tail cursor under exact ring distinctness, and the real post-state
`ring_shape_wf` is reconstructed separately for all ready, delayed, pending,
and suspended rings.

The public generic theorem needs exactly cursor-general core well-formedness
and membership of the pending Event node.  Managed gate and managed phase
corollaries derive those facts without using `resume_pending_gate_entry_rel`,
without equating `managed` and `sa_live`, and without claiming old-policy
`core_wf` for the real cursor state.

## Theorem-object audit

| theorem | premises | hidden hypotheses |
| --- | ---: | ---: |
| `canonical_tail_cursor_remove` | 1 | 0 |
| `pending_generic_key_abs_canonicalize_scheduler_cursors` | 0 | 0 |
| `canonicalize_scheduler_cursors_resume_one_pending_abs` | 1 | 0 |
| `cursor_general_core_wf_resume_one_pending_abs` | 2 | 0 |
| `CursorGeneralStrongResumePendingManagedGateRel_reentry_coreD` | 2 | 0 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_reentry_coreD` | 2 | 0 |

The embedded ML ledger checks `1/0/1/2/2/2`, with zero hidden hypotheses.
The private tail-cursor helper has the sharp premise `distinct (ring q)` over
`q :: 'tid node_ring`; the original cursor position is irrelevant because the
proof shadow overwrites it.  Distinctness remains necessary in the presence of
duplicate nodes.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Reentry_Core` has sole parent
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Body`, one theory,
`document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=120`.  The repository wrapper was bounded at 300 seconds and invoked
Isabelle with `-o quick_and_dirty=false -j 1`.

| run | exit | wrapper | first result |
| --- | ---: | ---: | --- |
| `20260811Tresume-managed-reentry-core-01-canonical-shadow` | 1 | 193.444 s | helper inferred over arbitrary xlists; `tail_cursor_wf` requires `node_ring` |
| `20260811Tresume-managed-reentry-core-02-sharp-node-ring` | 1 | 180.948 s | tail proof passed; captured-key normalization remained in commute simp |
| `20260811Tresume-managed-reentry-core-03-key-normalization` | 0 | 182.762 s | green; leaf 5 s |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `4DCCBBD87AB22FA054CE93A98F702E08A4837638BEE9B90899EE47D36F321941` |
| `command.txt` | `328DE406285AB5B23F6D4E58351DA88BEC8EE81A6FE83A43804BBAF380872D17` |
| `status.txt` | `8A2AF99EE7D7773E1E1D6290C1B72467D2D012C2D85B932469911EBDB55B9C0C` |
| `stdout.log` | `908486BCA36282450D2AE300489DEF8D3839B6E50EAC9041C5082A1AF6617167` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

## Exact remaining boundary

Cursor-general core preservation is now available for the managed body head.
The next re-entry rungs must transport the managed domain and strong
role/wake/one-due projections from `a` to `resume_one_pending_abs t a`, then
reconstruct the public shadow and strong snapshot at the exact ready-inserted
concrete state.  The iterative phase should retain the literal drained context
and snapshot; it must not reintroduce the legacy resume gate.
