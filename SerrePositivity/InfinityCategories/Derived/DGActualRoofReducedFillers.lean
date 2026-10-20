module
public import SerrePositivity.InfinityCategories.Derived.DGActualRoofClosedCoefficients
public import SerrePositivity.InfinityCategories.Derived.DGQuotientActualRoofTransportedFillers

/-! # 任意の実屋根相対問題の還元後の実充填

概要：共通 fiber へ還元した相対境界問題に、一つの追加閉分母後の実充填を供給する。
方針：回収した同じ閉分母の係数正方形を既存の有限相対充填へ渡す。
規約：正の単体次数。元の相対問題への輸送の合成は別工程。使われ方：屋根比較の弱同値判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGQuotient DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D] (P : Set D) (x y : D) {n : ℕ}
variable {a : (∂Δ[n + 1] : SSet.{max u v}) ⟶ dgRoofCorrespondence A D P x y}
variable {g : (Δ[n + 1] : SSet.{max u v}) ⟶ dgQuotientRoofCorrespondence A D P x y}

/-- 還元後の任意の正次数相対問題は追加閉分母後に実充填と全境界付き輸送を持つ。 -/
theorem dgActualRoofReducedFiller_exists (hP : localKFlat A D P)
    (R : DGActualRoofFiberReduction A D P x y (∂Δ[n + 1]).ι a g) :
    ∃ s' : DGClosedVerdierDenominators A D P x,
      ∃ r : s' ⟶ dgActualRoofReductionDenominator A D P x y R,
        ∃ t : (DGNerve.pinchedHom A D (ForgetEnrichment.to (Complex A) s'.obj.left) y) _⦋n + 1⦌,
          Nonempty (DGActualRoofTransportedFiller A D P x y r
            (dgActualRoofClosedSourceCoefficient A D P x y R)
            (SSet.yonedaEquiv (dgActualRoofClosedTargetCoefficient A D P x y R)) t) := by
  have hb : dgActualRoofClosedSourceCoefficient A D P x y R ≫
      pinchedHomChainMap ((inclusion A D P).map
        (ForgetEnrichment.to (Complex A)
          (dgActualRoofReductionDenominator A D P x y R).obj.left) y) =
        (∂Δ[n + 1]).ι ≫ SSet.yonedaEquiv.symm
          (SSet.yonedaEquiv (dgActualRoofClosedTargetCoefficient A D P x y R)) := by
    rw [Equiv.symm_apply_apply]
    exact dgActualRoofClosedCoefficient_square A D P x y R
  obtain ⟨s', r, t, hF⟩ := dgQuotientRoofFinite_exists_transportedFillerData A D P hP
    (m := 1) x (fun _ => y) (dgActualRoofReductionDenominator A D P x y R)
    (fun _ => dgActualRoofClosedSourceCoefficient A D P x y R)
    (fun _ => SSet.yonedaEquiv (dgActualRoofClosedTargetCoefficient A D P x y R)) (fun _ => hb)
  exact ⟨s', r, t 0, hF 0⟩

end SerrePositivity.InfinityCategories
