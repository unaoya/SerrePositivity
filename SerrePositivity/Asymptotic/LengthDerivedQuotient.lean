module

public import SerrePositivity.Asymptotic.LengthSerreQuotient
public import SerrePositivity.CategoryTheory.SerreDerivedQuotient

/-!
# 長さ零のホモロジーをもつ対象による有界導来商

長さで制限された加群列の有界導来圏を、全ホモロジーの正規化長さが零の対象で割る。
実際の Serre 商関手を使い、有界 t 構造と冪等完備性を構成する。
自由列のランク商との比較は、この構成とは別途必要である。
-/

@[expose] public section

universe u w₁ w₂

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
open CategoryTheory.Idempotents Filter

variable {R : Type u} [CommRing R] {J : Ideal R}
  (lam : NormalizedLength R J) (s : ℕ → ℕ)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)
  [HasDerivedCategory.{w₁} (LengthBoundedSequence lam s)]
  [HasDerivedCategory.{w₂} (LengthSerreQuotient lam s U hU hs)]

/-- 全ホモロジーの正規化長さが零になる有界導来対象の部分圏。 -/
def lengthDerivedNull : ObjectProperty (DerivedCategory.Bounded (LengthBoundedSequence lam s)) :=
  triangulatedKernel (boundedExactDerived (lengthSerreQuotientFunctor lam s U hU hs))

instance : (lengthDerivedNull lam s U hU hs).IsTriangulated := by
  unfold lengthDerivedNull
  infer_instance

instance : (lengthDerivedNull lam s U hU hs).IsClosedUnderIsomorphisms := by
  unfold lengthDerivedNull
  infer_instance

/-- 核の定義を、各次数の実数値の正規化長さで言い換える。 -/
lemma lengthDerivedNull_iff (X : DerivedCategory.Bounded (LengthBoundedSequence lam s)) :
    lengthDerivedNull lam s U hU hs X ↔
      ∀ q : ℤ, sequenceLength lam s U
        ((DerivedCategory.homologyFunctor (LengthBoundedSequence lam s) q).obj X.obj) = 0 := by
  rw [lengthDerivedNull, boundedExactDerived_kernel_iff]
  exact forall_congr' (fun q ↦ lengthSerreQuotient_isZero_iff lam s U hU hs _)

/-- 長さ零のホモロジーによる有界導来商。 -/
abbrev LengthDerivedQuotient := (lengthDerivedNull lam s U hU hs).trW.Localization

/-- 長さの導来商上の t 構造。 -/
noncomputable def lengthDerivedQuotientTStructure :
    TStructure (LengthDerivedQuotient lam s U hU hs) :=
  serreDerivedQuotientTStructure (lengthSerreQuotientFunctor lam s U hU hs)

/-- 長さの導来商の t 構造は有界。 -/
lemma lengthDerivedQuotient_bounded (X : LengthDerivedQuotient lam s U hU hs) :
    (lengthDerivedQuotientTStructure lam s U hU hs).bounded X :=
  serreDerivedQuotient_bounded _ X

/-- 長さの導来商は冪等完備。 -/
lemma lengthDerivedQuotient_isIdempotentComplete :
    IsIdempotentComplete (LengthDerivedQuotient lam s U hU hs) :=
  serreDerivedQuotient_isIdempotentComplete _

/-- 形式的直和因子を、長さで制限された加群列の有界導来対象で代表する。 -/
lemma lengthDerivedQuotientKaroubi_has_representative
    (Y : Karoubi (LengthDerivedQuotient lam s U hU hs)) :
    ∃ X : DerivedCategory.Bounded (LengthBoundedSequence lam s),
      Nonempty ((toKaroubi _).obj ((lengthDerivedNull lam s U hU hs).trW.Q.obj X) ≅ Y) :=
  serreDerivedQuotientKaroubi_has_representative _ Y

end SerrePositivity.Asymptotic
