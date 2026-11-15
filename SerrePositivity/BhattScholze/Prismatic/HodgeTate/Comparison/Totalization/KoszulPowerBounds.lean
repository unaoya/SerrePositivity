module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FixedTorBounds
public import SerrePositivity.HomologicalAlgebra.CochainTensorScalarCone

/-!
# 有限 Koszul 列の冪の一様な下界

## 概要
有限列の Koszul コホモロジーの下界は、各元を同じ冪に置き換えても変わらない。

## 方針
スカラー錐と残りの Koszul の指定テンソル同型を使い、主元の冪の評価を有限帰納する。

## 規約
正則性は仮定しない。列の長さを下界から重ねて差し引かない。

## 使われ方
BS 著者版 Lemma 4.22 の有限列の冪 Koszul 塔の一様な下界。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.DerivedCompletion

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
variable {R : Type u} [CommRing R]

/-- スカラー錐と有限 Koszul の交換は、既存のテンソル比較と結合・対称性の合成である。 -/
def scalarConeKoszulIso (a : R) {r : ℕ} (x : Fin r → R) (K : Complex R) :
    (scalarConeFunctor a).obj (koszulComplexOn x K) ≅
      koszulComplexOn x ((scalarConeFunctor a).obj K) := by
  let U : Complex R := CochainComplex.mappingCone (smulId a (cochainTensorUnit (R := R)))
  let P : Complex R := koszulComplex x
  exact (cochainTensorUnitScalarConeIso a (koszulComplexOn x K)).symm ≪≫
    (cochainTensorFixedLeft U).mapIso (koszulCochainTensorIso x K).symm ≪≫
    (α_ U P K).symm ≪≫
    (cochainTensorFixedRight K).mapIso (cochainTensorSymmetry U P) ≪≫
    (α_ P U K) ≪≫
    (cochainTensorFixedLeft P).mapIso (cochainTensorUnitScalarConeIso a K) ≪≫
    koszulCochainTensorIso x ((scalarConeFunctor a).obj K)

/-- 有限 Koszul 列の下界は、全ての冪について同じ数値で成り立つ。 -/
theorem koszulPowers_lowerBound {r : ℕ} (x : Fin r → R) (K : Complex R) (b : ℤ)
    (h : ∀ i : ℤ, i < b → IsZero ((koszulComplexOn x K).homology i))
    (n : ℕ) (i : ℤ) (hi : i < b) :
    IsZero ((koszulComplexOn (fun j => x j ^ n) K).homology i) := by
  revert n i
  induction r generalizing K with
  | zero => intro n i hi; exact h i hi
  | succ r ih =>
    intro n i hi
    let a := x (Fin.last r)
    let y := Fin.init x
    have hstart : ∀ j : ℤ, j < b →
        IsZero ((koszulComplexOn y ((scalarConeFunctor a).obj K)).homology j) := by
      intro j hj
      exact (h j hj).of_iso
        ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) j).mapIso (scalarConeKoszulIso a y K)).symm
    have hinit : ∀ j : ℤ, j < b →
        IsZero ((koszulComplexOn (fun k => y k ^ n) ((scalarConeFunctor a).obj K)).homology j) := by
      intro j hj
      exact ih y ((scalarConeFunctor a).obj K) hstart n j hj
    have hback : ∀ j : ℤ, j < b →
        IsZero (((scalarConeFunctor a).obj (koszulComplexOn (fun k => y k ^ n) K)).homology j) := by
      intro j hj
      exact (hinit j hj).of_iso
        ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) j).mapIso
          (scalarConeKoszulIso a (fun k => y k ^ n) K))
    exact scalarPowerCone_lowerBound a (koszulComplexOn (fun k => y k ^ n) K) b hback n i hi

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
