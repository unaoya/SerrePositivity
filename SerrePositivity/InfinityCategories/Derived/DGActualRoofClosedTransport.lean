module
public import SerrePositivity.InfinityCategories.Derived.DGActualRoofCoefficientTransport

/-! # 閉係数表示から元の相対問題への厳密な輸送

概要：回収した閉分母上の実係数と元の屋根図式を、境界全体で整合するホモトピーで結ぶ。
方針：実屋根包含の同定で始端だけを戻し、還元で構成した同じ全時刻の射を保つ。
規約：二つの輸送の境界比較は厳密な等式。使われ方：相対充填を元の問題へ戻す。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet MonoidalCategory
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (P : Set D) (x y : D) {L K : SSet.{max u v}}
variable {i : L ⟶ K} {a : L ⟶ dgRoofCorrespondence A D P x y}
variable {g : K ⟶ dgQuotientRoofCorrespondence A D P x y}
variable (R : DGActualRoofFiberReduction A D P x y i a g)

/-- 閉係数上の元境界から、元の実屋根境界への同じ全時刻の輸送。 -/
def dgActualRoofClosedBoundaryTransport : SSet.Homotopy
    (dgActualRoofClosedSourceCoefficient A D P x y R ≫
      dgClosedRoofHomInclusion A D P x y (dgActualRoofReductionDenominator A D P x y R)) a where
  h := R.boundaryTransport.h
  h₀ := R.boundaryTransport.h₀.trans
    (dgActualRoofClosedSourceCoefficient_inclusion A D P x y R).symm
  h₁ := R.boundaryTransport.h₁
  rel := by
    ext n s
    exact False.elim s.1.property

/-- 閉係数上の商全体から、元の実商屋根全体への同じ全時刻の輸送。 -/
def dgActualRoofClosedTargetTransport : SSet.Homotopy
    (dgActualRoofClosedTargetCoefficient A D P x y R ≫
      dgQuotientClosedRoofHomInclusion A D P x y
        (dgActualRoofReductionDenominator A D P x y R)) g where
  h := R.targetTransport.h
  h₀ := R.targetTransport.h₀.trans (dgActualRoofClosedTargetCoefficient_inclusion A D P x y R).symm
  h₁ := R.targetTransport.h₁
  rel := by
    ext n s
    exact False.elim s.1.property

/-- 閉係数表示での輸送も境界全体・全時刻で比較と厳密に可換。 -/
lemma dgActualRoofClosedTransport_boundary :
    (i ▷ (Δ[1] : SSet.{max u v})) ≫ (dgActualRoofClosedTargetTransport A D P x y R).h =
      (dgActualRoofClosedBoundaryTransport A D P x y R).h ≫ dgRoofCorrespondenceMap A D P x y :=
  R.transport_boundary

end SerrePositivity.InfinityCategories
