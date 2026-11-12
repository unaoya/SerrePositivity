module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofHomotopyRelativeFiller
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofCompatibleTransportComposite
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGActualRoofReducedFillers
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGActualRoofClosedTransport

/-! # 任意の実屋根比較正方形の全境界付き相対充填

概要：正次数の任意の実屋根比較正方形に、境界整合的な実充填と二輸送を供給する。
方針：共通 fiber 還元後の追加分母充填を、元の問題への輸送と相対合成する。
規約：弱同値性自体はここで主張しない。使われ方：全境界に対する弱い持ち上げ判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient SSet MonoidalCategory
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 正次数の任意の実屋根比較正方形に、全境界整合的なホモトピー相対充填が存在する。 -/
theorem dgActualRoofHomotopyRelativeFiller_nonempty (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    (x y : D) {n : ℕ}
    (a : (∂Δ[n + 1] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P x y)
    (g : (Δ[n + 1] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondence A D P x y)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y = (∂Δ[n + 1]).ι ≫ g) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofHomotopyRelativeFiller (∂Δ[n + 1]).ι
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y) a g) := by
  obtain ⟨R⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgActualRoofFiberReduction_nonempty A D P x y (∂Δ[n + 1]).ι a g ha
  obtain ⟨s', r, t, ⟨H⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgActualRoofReducedFiller_exists A D P x y hP R
  let u := SSet.yonedaEquiv.symm t ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion A D P x y s'
  let lA : SSet.Homotopy ((∂Δ[n + 1]).ι ≫ u)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgActualRoofClosedSourceCoefficient A D P x y R ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion A D P x y (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgActualRoofReductionDenominator A D P x y R)) := {
    h := H.relative.boundary_transport.h
    h₀ := by
      change SSet.ι₀ ≫ H.relative.boundary_transport.h = (∂Δ[n + 1]).ι ≫ u
      simpa only [u, Category.assoc] using H.relative.boundary_transport.h₀
    h₁ := H.relative.boundary_transport.h₁
    rel := by ext d s; exact False.elim s.1.property }
  let lK : SSet.Homotopy (u ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgActualRoofClosedTargetCoefficient A D P x y R ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientClosedRoofHomInclusion A D P x y
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgActualRoofReductionDenominator A D P x y R)) := {
    h := H.homotopy.h
    h₀ := by
      change SSet.ι₀ ≫ H.homotopy.h = u ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y
      simpa only [u, Category.assoc] using H.homotopy.h₀
    h₁ := by
      change SSet.ι₁ ≫ H.homotopy.h = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgActualRoofClosedTargetCoefficient A D P x y R ≫ _
      simpa only [Equiv.symm_apply_apply] using H.homotopy.h₁
    rel := by ext d s; exact False.elim s.1.property }
  have hb : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgActualRoofClosedSourceCoefficient A D P x y R ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((inclusion A D P).map
        (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgActualRoofReductionDenominator A D P x y R).obj.left) y) =
      (∂Δ[n + 1]).ι ≫ SSet.yonedaEquiv.symm
        (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgActualRoofClosedTargetCoefficient A D P x y R)) := by
    rw [Equiv.symm_apply_apply]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgActualRoofClosedCoefficient_square A D P x y R
  have hl : ((∂Δ[n + 1]).ι ▷ (Δ[1] : SSet.{max u v})) ≫ lK.h =
      lA.h ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y := by
    change ((∂Δ[n + 1]).ι ▷ Δ[1]) ≫ H.homotopy.h =
      H.relative.boundary_transport.h ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y
    exact H.homotopy_boundary A D hb
  obtain ⟨C⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofCompatibleTransportComposite_nonempty
    (i := (∂Δ[n + 1]).ι) (F := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y) (lA := lA)
    (rA := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgActualRoofClosedBoundaryTransport A D P x y R) (lK := lK)
    (rK := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgActualRoofClosedTargetTransport A D P x y R) hl
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgActualRoofClosedTransport_boundary A D P x y R)
  exact ⟨⟨u, C.source, C.target, C.boundary⟩⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
