import Poe.Examples.HelloWorld
import Poe.Prelude

/-!
# HelloWorld with Decidable WellFormed and evidence-producing parser

`validatorE` takes a single `ctx : Data` — no ghost precondition.
`WellFormed` is made decidable via boolean decision procedures, so the
`if h : WellFormed ctx` compiles. In the true branch the proof `h` is
immediately consumed by `parse`, which extracts structured values in one
traversal; `validatorCore` then works entirely on `ByteArray` and
`List ByteArray` with no `Data` in scope.

Two key theorems:
- `validatorE_bad`:  `¬WellFormed ctx → validatorE ctx = abort ()`
- `validatorE_good`: `WellFormed ctx  → validatorE ctx = check (validatorCore (parse ctx h))`

The first is only provable here (not with the ghost-precondition style)
because the else branch is explicit Lean code, not an invisible UPLC
unreachable node.
-/

namespace Poe.Experiments.HelloWorldParsed

open Poe.PlutusData (Data IsByteStringList)
open Poe.Examples.HelloWorld
    (WellFormed TxInfoOk RedeemerOk ScriptInfoOk
     decodeMessage decodeSignatories decodeOwner)
open Poe.Lib.DataDecoding (elemBytes)

-- ── Boolean decision procedures ──────────────────────────────────────

private def redeemerOkB : Data → Bool
  | .constr _ [.b _] => true
  | _                => false

private def allAreB : List Data → Bool
  | []        => true
  | .b _ :: t => allAreB t
  | _    :: _ => false

private def extractBss : List Data → List ByteArray
  | []        => []
  | .b b :: t => b :: extractBss t
  | _    :: t => extractBss t

private def isByteStringListB : Data → Bool
  | .list xs => allAreB xs
  | _        => false

private def txInfoOkB : Data → Bool
  | .constr _ (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: s :: _) => isByteStringListB s
  | _                                                            => false

private def scriptInfoOkB : Data → Bool
  | .constr _ [_, .constr _ [.constr _ [.b _]]] => true
  | _                                            => false

private def wellFormedB : Data → Bool
  | .constr 0 [t, r, s] => txInfoOkB t && redeemerOkB r && scriptInfoOkB s
  | _                    => false

-- ── Correctness of the decision procedures ───────────────────────────

private theorem redeemerOkB_iff (d : Data) : redeemerOkB d = true ↔ RedeemerOk d := by
  constructor
  · intro h
    simp only [redeemerOkB] at h
    split at h
    · trivial
    · exact absurd h (by decide)
  · intro h
    simp only [RedeemerOk] at h
    split at h
    · rfl
    · exact h.elim

private theorem allAreB_extractBss (xs : List Data) (h : allAreB xs = true) :
    xs = (extractBss xs).map .b := by
  induction xs with
  | nil => simp [extractBss]
  | cons x rest ih =>
    cases x with
    | b b        =>
      simp only [allAreB] at h
      calc .b b :: rest
          = .b b :: (extractBss rest).map .b := congrArg (.b b :: ·) (ih h)
        _ = (b :: extractBss rest).map .b    := rfl
        _ = (extractBss (.b b :: rest)).map .b := rfl
    | constr _ _ => simp [allAreB] at h
    | list _     => simp [allAreB] at h
    | i _        => simp [allAreB] at h

private theorem allAreB_of_map (bss : List ByteArray) : allAreB (bss.map .b) = true := by
  induction bss with
  | nil         => simp [allAreB]
  | cons _ _ ih => simp [allAreB, ih]

private theorem isByteStringListB_iff (d : Data) :
    isByteStringListB d = true ↔ IsByteStringList d := by
  constructor
  · intro h
    cases d with
    | list xs =>
      simp only [isByteStringListB] at h
      exact ⟨extractBss xs, congrArg Data.list (allAreB_extractBss xs h)⟩
    | _ => simp only [isByteStringListB] at h; exact absurd h (by decide)
  · rintro ⟨bss, rfl⟩
    simp only [isByteStringListB]
    exact allAreB_of_map bss

private theorem txInfoOkB_iff (d : Data) : txInfoOkB d = true ↔ TxInfoOk d := by
  constructor
  · intro h
    simp only [txInfoOkB] at h
    split at h
    · simp only [TxInfoOk]; exact (isByteStringListB_iff _).mp h
    · exact absurd h (by decide)
  · intro h
    simp only [TxInfoOk] at h
    split at h
    · simp only [txInfoOkB]; exact (isByteStringListB_iff _).mpr h
    · exact h.elim

private theorem scriptInfoOkB_iff (d : Data) : scriptInfoOkB d = true ↔ ScriptInfoOk d := by
  constructor
  · intro h
    simp only [scriptInfoOkB] at h
    split at h
    · trivial
    · exact absurd h (by decide)
  · intro h
    simp only [ScriptInfoOk] at h
    split at h
    · rfl
    · exact h.elim

private theorem wellFormedB_iff (ctx : Data) : wellFormedB ctx = true ↔ WellFormed ctx := by
  constructor
  · intro h
    simp only [wellFormedB] at h
    split at h
    · simp only [Bool.and_eq_true] at h
      simp only [WellFormed]
      exact ⟨(txInfoOkB_iff _).mp h.1.1, (redeemerOkB_iff _).mp h.1.2,
             (scriptInfoOkB_iff _).mp h.2⟩
    · exact absurd h (by decide)
  · intro h
    simp only [WellFormed] at h
    split at h
    · simp only [wellFormedB, Bool.and_eq_true]
      exact ⟨⟨(txInfoOkB_iff _).mpr h.1, (redeemerOkB_iff _).mpr h.2.1⟩,
             (scriptInfoOkB_iff _).mpr h.2.2⟩
    · exact h.elim

instance (ctx : Data) : Decidable (WellFormed ctx) :=
  decidable_of_iff (wellFormedB ctx = true) (wellFormedB_iff ctx)

-- ── Evidence structure and parser ────────────────────────────────────

/-- The values extracted from a well-formed `ScriptContext`. -/
structure Evidence where
  msg   : ByteArray
  owner : ByteArray
  sigs  : List ByteArray

/-- Total decoder: consumes the proof `h` to feed ghost preconditions
    to each field accessor, producing structured values in one pass. -/
def parse (ctx : Data) (h : WellFormed ctx) : Evidence :=
  match ctx, h with
  | .constr 0 [txInfo, redeemer, scriptInfo], ⟨hTx, hRed, hSI⟩ =>
    { msg   := decodeMessage redeemer hRed
      owner := decodeOwner scriptInfo hSI
      sigs  := decodeSignatories txInfo hTx }

-- ── Core logic and deployable entry point ────────────────────────────

/-- Business logic on structured types — no `Data` in scope. -/
def validatorCore (e : Evidence) : Bool :=
  e.msg == "Hello, World!".toUTF8 && elemBytes e.owner e.sigs

/-- Deployable validator: single `Data` argument, one wellformedness
    check, proof flows to `parse`, core logic sees only `Evidence`. -/
def validatorE (ctx : Data) : Unit :=
  if h : WellFormed ctx then
    Poe.Prelude.check (validatorCore (parse ctx h))
  else
    Poe.Prelude.abort ()

-- ── Key theorems ─────────────────────────────────────────────────────

theorem validatorE_bad (ctx : Data) (h : ¬WellFormed ctx) :
    validatorE ctx = Poe.Prelude.abort () := by
  simp only [validatorE, dif_neg h]

theorem validatorE_good (ctx : Data) (h : WellFormed ctx) :
    validatorE ctx = Poe.Prelude.check (validatorCore (parse ctx h)) := by
  simp only [validatorE, dif_pos h]

end Poe.Experiments.HelloWorldParsed
