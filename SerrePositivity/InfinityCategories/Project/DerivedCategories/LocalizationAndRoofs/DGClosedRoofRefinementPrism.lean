module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGClosedPrecompositionSlicePrism
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierClosedRefinementEdge
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGClosedRoofHomInclusion

/-! # 指定閉細分に沿う元の実屋根の全係数 prism

概要：指定閉細分の前合成と元の Hom 包含を、実屋根内の全次数のホモトピーで結ぶ。
方針：固定標的の slice prism と元の指定実分母辺を、始域射影の一致で貼る。
規約：全係数単体・全端点を保持する。使われ方：有限相対充填の実全空間への移行。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded SSet MonoidalCategory
open CartesianMonoidalCategory
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable (P : Set D) (x y : D) {s t : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x} (r : s ⟶ t)

/-- 指定閉細分に沿う、元の Hom 全体の実屋根内の prism。 -/
def dgClosedRoofRefinementPrism :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D (ForgetEnrichment.to (Complex A) t.obj.left) y ⊗ Δ[1] ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P x y :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecompositionSlicePrism A D y r.hom.left)
    (snd _ Δ[1] ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorEdge A D P x r).edge) (by
      have h : SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorEdge A D P x r).edge ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x =
          (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D r.hom.left).edge :=
        (SSet.yonedaEquiv_symm_comp _ _).trans
          (congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorEdge_source A D P x r))
      exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecompositionSlicePrism_source A D y r.hom.left).trans
        ((congrArg (fun f => snd _ Δ[1] ≫ f) h).symm.trans (Category.assoc _ _ _).symm))

/-- 全係数の実屋根 prism の分子成分は、元の指定閉前合成の slice prism。 -/
lemma dgClosedRoofRefinementPrism_target :
    dgClosedRoofRefinementPrism A D P x y r ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceTarget A D P x y =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecompositionSlicePrism A D y r.hom.left :=
  pullback.lift_fst _ _ _

/-- 全係数の実屋根 prism は、元の指定実分母辺に沿う。 -/
lemma dgClosedRoofRefinementPrism_projection :
    dgClosedRoofRefinementPrism A D P x y r ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceProjection A D P x y =
      snd _ Δ[1] ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorEdge A D P x r).edge :=
  pullback.lift_snd _ _ _

/-- 実屋根 prism の零端点は、指定閉細分による全係数の前合成の包含。 -/
lemma dgClosedRoofRefinementPrism_zero :
    SSet.ι₀ ≫ dgClosedRoofRefinementPrism A D P x y r =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A D (y := y) r.hom.left ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion A D P x y s := by
  apply pullback.hom_ext
  · change (SSet.ι₀ ≫ dgClosedRoofRefinementPrism A D P x y r) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceTarget A D P x y =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A D (y := y) r.hom.left ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion A D P x y s) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceTarget A D P x y
    simp only [Category.assoc, dgClosedRoofRefinementPrism_target,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecompositionSlicePrism_zero, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion_target]
    rfl
  · change (SSet.ι₀ ≫ dgClosedRoofRefinementPrism A D P x y r) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceProjection A D P x y =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A D (y := y) r.hom.left ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion A D P x y s) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceProjection A D P x y
    simp only [Category.assoc, dgClosedRoofRefinementPrism_projection,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEdgeCylinder_zero, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion_projection, SSet.comp_const]

/-- 実屋根 prism の一端点は、元の全係数の包含。 -/
lemma dgClosedRoofRefinementPrism_one :
    SSet.ι₁ ≫ dgClosedRoofRefinementPrism A D P x y r =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion A D P x y t := by
  apply pullback.hom_ext
  · change (SSet.ι₁ ≫ dgClosedRoofRefinementPrism A D P x y r) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceTarget A D P x y =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion A D P x y t ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceTarget A D P x y
    simp only [Category.assoc, dgClosedRoofRefinementPrism_target,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecompositionSlicePrism_one, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion_target]
  · change (SSet.ι₁ ≫ dgClosedRoofRefinementPrism A D P x y r) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceProjection A D P x y =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion A D P x y t ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceProjection A D P x y
    simp only [Category.assoc, dgClosedRoofRefinementPrism_projection,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEdgeCylinder_one, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion_projection]

/-- 指定閉細分による全次数の前合成は、実屋根内で元の係数包含とホモトピック。 -/
def dgClosedRoofRefinementHomotopy :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A D (y := y) r.hom.left ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion A D P x y s) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion A D P x y t) where
  h := dgClosedRoofRefinementPrism A D P x y r
  h₀ := dgClosedRoofRefinementPrism_zero A D P x y r
  h₁ := dgClosedRoofRefinementPrism_one A D P x y r
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.2

end SerrePositivity.InfinityCategories.Project.DerivedCategories
