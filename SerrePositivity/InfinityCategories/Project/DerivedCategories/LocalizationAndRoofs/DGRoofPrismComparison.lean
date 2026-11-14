module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SliceComparisons.DGClosedSlicePrismGeneral
public import SerrePositivity.InfinityCategories.Project.Entrypoints.DGWalkingHomPrismNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGClosedPrecompositionSlicePrism
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGStrictNatTransSliceWhisker
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGClosedRoofRefinementPrism
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientClosedRoofRefinementPrism
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGRoofCorrespondenceMap

/-! # 実屋根の全係数細分 prism と商比較

概要：元の実屋根の全 prism を商へ写すことと、商の係数 prism は厳密に一致。
方針：分子は固定標的 slice の自然性、分母は元の指定分母辺への射影で比較する。
規約：全係数・全時刻の写像等式。使われ方：有限相対充填の二輸送の境界整合性。
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

/-- 全次数の閉細分 prism は実屋根の商比較と厳密に可換する。 -/
lemma dgClosedRoofRefinementPrism_comparison :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofRefinementPrism A D P x y r ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((DGQuotient.inclusion A D P).map
        (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) t.obj.left) y) ▷ (Δ[1] : SSet.{max u v})) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientClosedRoofRefinementPrism A D P x y r := by
  let j := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((DGQuotient.inclusion A D P).map
    (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) t.obj.left) y)
  apply pullback.hom_ext
  · change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofRefinementPrism A D P x y r ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceTarget A D P x y =
      ((j ▷ Δ[1]) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientClosedRoofRefinementPrism A D P x y r) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceTarget A D P x y
    have hm : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceTarget A D P x y =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceTarget A D P x y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientTargetSliceMap A D P y :=
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap_target A D P x y
    rw [Category.assoc, hm, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofRefinementPrism_target, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientClosedRoofRefinementPrism_target]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecompositionSlicePrism_naturality A D (DGQuotient.QuotientObject D P)
      (DGQuotient.inclusion A D P) y r.hom.left (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNervePoint A D P y)
  · change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofRefinementPrism A D P x y r ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceProjection A D P x y =
      ((j ▷ Δ[1]) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientClosedRoofRefinementPrism A D P x y r) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceProjection A D P x y
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap_projection,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofRefinementPrism_projection, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientClosedRoofRefinementPrism_projection, ← Category.assoc, whiskerRight_snd]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
