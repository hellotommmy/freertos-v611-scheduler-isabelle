# Resume managed modular endpoint — 2026-08-12

Baseline: `6a134f2` on `agent/universal-scheduler-refinement`.

## Checked scope

This exclusive child introduces the wrap-safe yield-count representation used
after managed pending drain and missed-tick replay.  The unbounded abstract
counter is preserved in a separate `yield_count_mod_rel`; the existing exact
cursor-general endpoint observes a state whose yield counter is normalized to
the low 32 bits.

The child defines both the public modular endpoint and the corresponding
protected modular tick-entry relation.  The protected relation remains a real
protected entry over a normalized public shadow; it does not assert a public
`0/0` endpoint at an actual protected `1/1` state.

The checked conversion surface contains:

- all scheduler-abstract selector equations for yield-count normalization;
- normalization idempotence;
- the proof-port overlay yield-count selector;
- exact-count normalization and modular-counter introduction;
- an exact endpoint yield-count destructor;
- exact public endpoint to modular endpoint conversion; and
- exact protected entry to modular protected entry conversion.

No theorem assumes no-wrap, uses the legacy managed gate relation, equates the
managed set with `sa_live`, or asserts the false commutation
`normalize_yield_count_abs (request_yield a) =
 request_yield (normalize_yield_count_abs a)`.

At the wrap witness `sa_yield_count a = 2^32 - 1`, a concrete all-ones word
advances to zero while the abstract counter advances to `2^32`.  The modular
relation retains that unbounded count, while the exact endpoint sees the
normalized zero count.

## Theorem-object audit

| theorem | premises | hidden hypotheses |
| --- | ---: | ---: |
| `normalize_yield_count_abs_components` | 0 | 0 |
| `normalize_yield_count_abs_idempotent` | 0 | 0 |
| `scheduler_port_overlay_yield_count` | 0 | 0 |
| `normalize_yield_count_abs_exactI` | 1 | 0 |
| `CursorGeneralStrongSchedulerEndpointRel_yield_countD` | 1 | 0 |
| `CursorGeneralStrongSchedulerEndpointRel_modularI` | 1 | 0 |
| `CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_modularI` | 1 | 0 |

The embedded ML ledger checks exactly `0/0/0/1/1/1/1`, with zero hidden
hypotheses.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Modular_Endpoint` has sole parent
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Replay_Split`, one theory,
`document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=120`.  The repository wrapper used a 600-second lifecycle budget and
Isabelle options `-o quick_and_dirty=false -j 1`.

An initial orchestration call was cut off by the tool transport after five
seconds, before the wrapper created a run directory or launched an Isabelle
process.  It left no matching Java, Poly/ML, Bash, or wrapper process and is
not checker evidence.  The sole completed checker run was green:

| run | exit | elapsed | result |
| --- | ---: | ---: | --- |
| `20260812Tresume-managed-modular-endpoint-02-foundation` | 0 | 267.616 s | green; parent 14 s, leaf 4 s |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `16516BE83CE24EBFC49DBCF07B2D66229DDF8EBF76144E3CA2957BD27C42A5F3` |
| `command.txt` | `CCB983B2115D79F1DC3B8AD27FA686AEE37AF702BBAFB45F2A252A939EF6B327` |
| `status.txt` | `479512D21C8E79C3B2169AA6CD33D4C3854246260E6A5EE36F5ED4A17162DAEF` |
| `stdout.log` | `3286209642E8CB819C7D5F0FF01EBC95C01CA13E36A62C893BF92B0252A01FC7` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

Frozen-layout evidence recorded by the final status:

- ELF: `DC830E50513384D712E0D1C68CB198EA656365F673D021C452D7D7EBD45C045A`
- ledger: `CA288A4CD2344BE979ADFA9DBF0298C6715F196D64AE472D173304289C4F2C02`
- generated address configuration:
  `27F74768E1DB1C3F8DBFCFC85371075192BB7D2544ED324DC81B65A9A2911712`

## Exact remaining boundary

The next child transports the protected modular relation across the literal
`xMissedYield` clear while pairing it with the abstract update
`sa_missed_yield := False`.  A later child handles the literal `y = 1` yield
branch by directly rebuilding the normalized post snapshot and applying
`yield_count_mod_rel_request`; it must not commute normalization through
`request_yield`.
