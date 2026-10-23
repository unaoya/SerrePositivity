module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.NervePresentationNaturality
public import SerrePositivity.InfinityCategories.F1.Simplicial.SimplexNerveRestrictionOver

/-!
概要：元の標準単体上の全 native Hom 比較の、全ての単体写像に沿う指定自然性。
方針：同じ有限鎖表示の可換正方形へ既存の局所自然性を適用する。
規約：大域から制限された像に限定せず、元の全局所 Hom を使う。
使われ方：境界の共有面で分類比較を揃える。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{u} C] {m n : ℕ}
  (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) (σ : (Δ[n] : SSet.{u}) ⟶ nerve C)
  (p q : CocartesianFibrationCategory (nerve C))
local notation "P" => cocartesianStrictTransportCoherentDiagram p.val.hom
local notation "Q" => cocartesianStrictTransportCoherentDiagram q.val.hom

/-- 制限した標準単体の比較は、同じ合成関手の表示で移した比較そのもの。 -/
lemma cocartesianStandardSimplexHomComparison_restrictionPresentation :
    cocartesianStandardSimplexHomComparison (f ≫ σ) p q =
      cocartesianNervePresentationHomComparison (Over.mk (f ≫ σ))
        (simplexNerveMapFunctor f ⋙ simplexNerveBaseFunctor σ)
        (simplexNerveRestrictionOverIso f σ) p q :=
  (cocartesianStandardSimplexHomComparison_presentation p q (f ≫ σ)).trans
    (cocartesianNervePresentationHomComparison_eq_of_eq (Over.mk (f ≫ σ))
      (simplexNerveBaseFunctor (f ≫ σ)) (simplexNerveOverIso (f ≫ σ)) p q
      (simplexNerveBaseFunctor_comp f σ) (simplexNerveRestrictionOverIso f σ) rfl)

/-- 同じ元の全局所 Hom 比較は、任意の標準単体の射による直接制限に自然。 -/
def cocartesianStandardSimplexHomComparison_naturalityIso :
    FunctorIso
      (((cocartesianPullbackNativeCoreFunctor p.val.hom q.val.hom) ⋙
        SSet.uliftFunctor.{u + 1, u}).map
          (Over.homMk f rfl : Over.mk (f ≫ σ) ⟶ Over.mk σ).op ≫
          cocartesianStandardSimplexHomComparison (f ≫ σ) p q)
      (cocartesianStandardSimplexHomComparison σ p q ≫
        (intervalDiagramOverFunctor P Q).map (uliftOverMorphism
          (Over.homMk f rfl : Over.mk (f ≫ σ) ⟶ Over.mk σ)).op) := by
  apply F2.functorIsoOfEq
    (cocartesianNervePresentationHomComparison_naturalityIso
      (simplexNerveMapFunctor f) (simplexNerveBaseFunctor σ) p q
      (simplexNerveRestrictionOverIso f σ) (simplexNerveOverIso σ)
      (Over.homMk f rfl) (simplexNerveRestrictionOverIso_comm f σ))
  · rw [cocartesianStandardSimplexHomComparison_restrictionPresentation f σ p q]
  · rw [cocartesianStandardSimplexHomComparison_presentation p q σ]
    rfl

/-- 同じ底上の可換式で端点を指定した、全局所比較の自然性。 -/
def cocartesianStandardSimplexHomComparison_overNaturalityIso
    (τ : (Δ[m] : SSet.{u}) ⟶ nerve C) (h : f ≫ σ = τ) :
    FunctorIso
      (((cocartesianPullbackNativeCoreFunctor p.val.hom q.val.hom) ⋙
        SSet.uliftFunctor.{u + 1, u}).map
          (Over.homMk f h : Over.mk τ ⟶ Over.mk σ).op ≫
          cocartesianStandardSimplexHomComparison τ p q)
      (cocartesianStandardSimplexHomComparison σ p q ≫
        (intervalDiagramOverFunctor P Q).map (uliftOverMorphism
          (Over.homMk f h : Over.mk τ ⟶ Over.mk σ)).op) := by
  subst τ
  exact cocartesianStandardSimplexHomComparison_naturalityIso f σ p q

end SerrePositivity.InfinityCategories
