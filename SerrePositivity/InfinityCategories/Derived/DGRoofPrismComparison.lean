module
public import SerrePositivity.InfinityCategories.Derived.DGClosedSlicePrismNaturality
public import SerrePositivity.InfinityCategories.Derived.DGClosedRoofRefinementPrism
public import SerrePositivity.InfinityCategories.Derived.DGQuotientClosedRoofRefinementPrism
public import SerrePositivity.InfinityCategories.Derived.DGRoofCorrespondenceMap

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet MonoidalCategory
open CartesianMonoidalCategory
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (P : Set D) (x y : D) {s t : DGClosedVerdierDenominators A D P x} (r : s ⟶ t)

/-- 全次数の閉細分 prism は実屋根の商比較と厳密に可換する。 -/
lemma dgClosedRoofRefinementPrism_comparison :
    dgClosedRoofRefinementPrism A D P x y r ≫ dgRoofCorrespondenceMap A D P x y =
      (pinchedHomChainMap ((DGQuotient.inclusion A D P).map
        (ForgetEnrichment.to (Complex A) t.obj.left) y) ▷ (Δ[1] : SSet.{max u v})) ≫
        dgQuotientClosedRoofRefinementPrism A D P x y r := by
  let j := pinchedHomChainMap ((DGQuotient.inclusion A D P).map
    (ForgetEnrichment.to (Complex A) t.obj.left) y)
  apply pullback.hom_ext
  · change (dgClosedRoofRefinementPrism A D P x y r ≫
      dgRoofCorrespondenceMap A D P x y) ≫ dgQuotientRoofCorrespondenceTarget A D P x y =
      ((j ▷ Δ[1]) ≫ dgQuotientClosedRoofRefinementPrism A D P x y r) ≫
        dgQuotientRoofCorrespondenceTarget A D P x y
    have hm : dgRoofCorrespondenceMap A D P x y ≫
        dgQuotientRoofCorrespondenceTarget A D P x y =
        dgRoofCorrespondenceTarget A D P x y ≫ dgQuotientTargetSliceMap A D P y :=
      dgRoofCorrespondenceMap_target A D P x y
    rw [Category.assoc, hm, ← Category.assoc,
      dgClosedRoofRefinementPrism_target, Category.assoc,
      dgQuotientClosedRoofRefinementPrism_target]
    exact dgClosedPrecompositionSlicePrism_naturality A D (DGQuotient.QuotientObject D P)
      (DGQuotient.inclusion A D P) y r.hom.left (dgQuotientNervePoint A D P y)
  · change (dgClosedRoofRefinementPrism A D P x y r ≫
      dgRoofCorrespondenceMap A D P x y) ≫
        dgQuotientRoofCorrespondenceProjection A D P x y =
      ((j ▷ Δ[1]) ≫ dgQuotientClosedRoofRefinementPrism A D P x y r) ≫
        dgQuotientRoofCorrespondenceProjection A D P x y
    rw [Category.assoc, dgRoofCorrespondenceMap_projection,
      dgClosedRoofRefinementPrism_projection, Category.assoc,
      dgQuotientClosedRoofRefinementPrism_projection, ← Category.assoc, whiskerRight_snd]

end SerrePositivity.InfinityCategories
