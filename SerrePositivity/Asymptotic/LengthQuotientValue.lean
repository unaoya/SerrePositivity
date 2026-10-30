module

public import SerrePositivity.Asymptotic.LengthSerreQuotient
public import SerrePositivity.CategoryTheory.Abelian.SerreLength

/-!
# 加群列の Serre 商上の忠実な長さ

正規化超極限を Serre 商の全対象に降下させる。商での同型不変性、非負性、
短完全列での加法性を証明する。値が零になることと零対象であることも同値になる。
これは命題4.3の評価先の構成であり、評価元の Verdier 商との接続は含めない。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits Filter

variable {R : Type u} [CommRing R] {J : Ideal R}
  (lam : NormalizedLength R J) (s : ℕ → ℕ)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

/-- Serre 商上の実数値の長さ。 -/
noncomputable def lengthQuotientValue (X : LengthSerreQuotient lam s U hU hs) : ℝ :=
  haveI := zeroSequenceLength_isSerreClass lam s U hU hs
  serreQuotientLength (zeroSequenceLength lam s U) (sequenceLength lam s U) X

/-- 元の加群列の像では正規化超極限に一致する。 -/
@[simp] lemma lengthQuotientValue_obj (M : LengthBoundedSequence lam s) :
    lengthQuotientValue lam s U hU hs ((lengthSerreQuotientFunctor lam s U hU hs).obj M) =
      sequenceLength lam s U M := rfl

/-- 商上の長さは非負である。 -/
lemma lengthQuotientValue_nonneg (X : LengthSerreQuotient lam s U hU hs) :
    0 ≤ lengthQuotientValue lam s U hU hs X :=
  sequenceLength_nonneg lam s U hU hs _

/-- 商で新しく現れる同型に対しても長さは不変である。 -/
lemma lengthQuotientValue_iso {X Y : LengthSerreQuotient lam s U hU hs} (e : X ≅ Y) :
    lengthQuotientValue lam s U hU hs X = lengthQuotientValue lam s U hU hs Y := by
  let := zeroSequenceLength_isSerreClass lam s U hU hs
  exact serreQuotientLength_iso (zeroSequenceLength lam s U) (sequenceLength lam s U)
    (sequenceLength_iso lam s U) (sequenceLength_add lam s U hU hs) (fun _ h ↦ h) e

/-- 商の任意の短完全列に対して長さは加法的である。 -/
lemma lengthQuotientValue_add {S : ShortComplex (LengthSerreQuotient lam s U hU hs)}
    (hS : S.ShortExact) :
    lengthQuotientValue lam s U hU hs S.X₂ = lengthQuotientValue lam s U hU hs S.X₁ +
      lengthQuotientValue lam s U hU hs S.X₃ := by
  let := zeroSequenceLength_isSerreClass lam s U hU hs
  exact serreQuotientLength_add (zeroSequenceLength lam s U) (sequenceLength lam s U)
    (sequenceLength_iso lam s U) (sequenceLength_add lam s U hU hs) (fun _ h ↦ h) hS

/-- 商上では、長さが零であることと零対象であることが一致する。 -/
lemma lengthQuotientValue_eq_zero_iff (X : LengthSerreQuotient lam s U hU hs) :
    lengthQuotientValue lam s U hU hs X = 0 ↔ IsZero X := by
  let := zeroSequenceLength_isSerreClass lam s U hU hs
  exact serreQuotientLength_eq_zero_iff (zeroSequenceLength lam s U)
    (sequenceLength lam s U) (fun _ ↦ Iff.rfl) X

end SerrePositivity.Asymptotic
