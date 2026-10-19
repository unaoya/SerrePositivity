module
public import SerrePositivity.InfinityCategories.Derived.DGQuotientClosedRoofHomInclusion
public import SerrePositivity.InfinityCategories.Derived.DGQuotientPinchedSlice

/-! # 指定閉分母上の実 Hom 包含と商比較

概要：元の閉分母上の Hom 全体の包含は、商 Hom 鎖写像と実屋根比較に可換。
方針：分子成分の slice 自然性と定値分母の射影で pullback の二射影を比較する。
規約：全次数の写像の厳密な等式。使われ方：有限相対ホモトピーを実屋根へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 指定閉分母上の元の Hom の実屋根への包含は、実商比較と全次数で厳密に可換。 -/
lemma dgClosedRoofHomInclusion_comparison (P : Set D) (x y : D)
    (s : DGClosedVerdierDenominators A D P x) :
    dgClosedRoofHomInclusion A D P x y s ≫ dgRoofCorrespondenceMap A D P x y =
      pinchedHomChainMap ((DGQuotient.inclusion A D P).map
        (ForgetEnrichment.to (Complex A) s.obj.left) y) ≫
        dgQuotientClosedRoofHomInclusion A D P x y s := by
  apply pullback.hom_ext
  · have h : dgRoofCorrespondenceMap A D P x y ≫
        dgQuotientRoofCorrespondenceTarget A D P x y =
        dgRoofCorrespondenceTarget A D P x y ≫ dgQuotientTargetSliceMap A D P y :=
      dgRoofCorrespondenceMap_target A D P x y
    calc
      _ = (dgClosedRoofHomInclusion A D P x y s ≫ dgRoofCorrespondenceTarget A D P x y) ≫
          dgQuotientTargetSliceMap A D P y :=
        (Category.assoc _ _ _).trans
          ((congrArg (fun f => dgClosedRoofHomInclusion A D P x y s ≫ f) h).trans
            (Category.assoc _ _ _).symm)
      _ = _ := congrArg (fun f => f ≫ dgQuotientTargetSliceMap A D P y)
        (dgClosedRoofHomInclusion_target A D P x y s)
      _ = _ := dgQuotientTargetSliceMap_pinched A D P
        (ForgetEnrichment.to (Complex A) s.obj.left) y
      _ = _ := congrArg (fun f => pinchedHomChainMap ((DGQuotient.inclusion A D P).map
        (ForgetEnrichment.to (Complex A) s.obj.left) y) ≫ f)
          (dgQuotientClosedRoofHomInclusion_target A D P x y s).symm
      _ = _ := (Category.assoc _ _ _).symm
  · change (dgClosedRoofHomInclusion A D P x y s ≫ dgRoofCorrespondenceMap A D P x y) ≫
      dgQuotientRoofCorrespondenceProjection A D P x y =
      (pinchedHomChainMap ((DGQuotient.inclusion A D P).map
        (ForgetEnrichment.to (Complex A) s.obj.left) y) ≫
        dgQuotientClosedRoofHomInclusion A D P x y s) ≫
        dgQuotientRoofCorrespondenceProjection A D P x y
    rw [Category.assoc, dgRoofCorrespondenceMap_projection,
      dgClosedRoofHomInclusion_projection, Category.assoc,
      dgQuotientClosedRoofHomInclusion_projection, SSet.comp_const]

end SerrePositivity.InfinityCategories
