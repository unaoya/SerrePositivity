module

public import SerrePositivity.Asymptotic.SmallLengthSerreQuotient
public import SerrePositivity.CategoryTheory.SerreDerivedQuotient

/-!
# 通常の o(s) ホモロジーによる有界導来商

全次数のホモロジーの長さが通常の `o(s)` となる対象で有界導来圏を割る。
この商の有界 t 構造と冪等完備性に、分母保存の追加仮定は要らない。
支持つき自由列のランク商との同値はまだ別途必要である。
-/

@[expose] public section

universe u w₁ w₂

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
open CategoryTheory.Idempotents Filter Asymptotics

variable {R : Type u} [CommRing R] {J : Ideal R}
  (lam : NormalizedLength R J) (s : ℕ → ℕ)
  [HasDerivedCategory.{w₁} (LengthBoundedSequence lam s)]
  [HasDerivedCategory.{w₂} (SmallLengthSerreQuotient lam s)]

/-- 全ホモロジーの長さが通常の `o(s)` になる有界導来対象の部分圏。 -/
def smallLengthDerivedNull :
    ObjectProperty (DerivedCategory.Bounded (LengthBoundedSequence lam s)) :=
  triangulatedKernel (boundedExactDerived (smallLengthSerreQuotientFunctor lam s))

instance : (smallLengthDerivedNull lam s).IsTriangulated := by
  unfold smallLengthDerivedNull
  infer_instance

instance : (smallLengthDerivedNull lam s).IsClosedUnderIsomorphisms := by
  unfold smallLengthDerivedNull
  infer_instance

/-- 小さい導来対象の核の定義と、通常の `o(s)` ホモロジー条件との同値。 -/
lemma smallLengthDerivedNull_iff (X : DerivedCategory.Bounded (LengthBoundedSequence lam s)) :
    smallLengthDerivedNull lam s X ↔
      ∀ q : ℤ, smallSequenceLength lam s
        ((DerivedCategory.homologyFunctor (LengthBoundedSequence lam s) q).obj X.obj) :=
  serreDerived_kernel_iff (smallLengthSerreQuotientFunctor lam s) (smallSequenceLength lam s) X

/-- 通常の小さいホモロジーによる有界導来商。 -/
abbrev SmallLengthDerivedQuotient := (smallLengthDerivedNull lam s).trW.Localization

/-- 通常の小さいホモロジーによる商の t 構造。 -/
noncomputable def smallLengthDerivedQuotientTStructure :
    TStructure (SmallLengthDerivedQuotient lam s) :=
  serreDerivedQuotientTStructure (smallLengthSerreQuotientFunctor lam s)

/-- 通常の小さいホモロジーによる商の t 構造は有界。 -/
lemma smallLengthDerivedQuotient_bounded (X : SmallLengthDerivedQuotient lam s) :
    (smallLengthDerivedQuotientTStructure lam s).bounded X :=
  serreDerivedQuotient_bounded _ X

/-- 通常の小さいホモロジーによる商は冪等完備。 -/
lemma smallLengthDerivedQuotient_isIdempotentComplete :
    IsIdempotentComplete (SmallLengthDerivedQuotient lam s) :=
  serreDerivedQuotient_isIdempotentComplete _

/-- 形式的直和因子を有界導来圏の対象で代表する。 -/
lemma smallLengthDerivedQuotientKaroubi_has_representative
    (Y : Karoubi (SmallLengthDerivedQuotient lam s)) :
    ∃ X : DerivedCategory.Bounded (LengthBoundedSequence lam s),
      Nonempty ((toKaroubi _).obj ((smallLengthDerivedNull lam s).trW.Q.obj X) ≅ Y) :=
  serreDerivedQuotientKaroubi_has_representative _ Y

end SerrePositivity.Asymptotic
