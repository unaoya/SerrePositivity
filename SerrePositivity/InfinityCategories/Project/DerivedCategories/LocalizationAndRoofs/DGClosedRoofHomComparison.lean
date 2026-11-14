module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientClosedRoofHomInclusion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientPinchedSlice

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded SSet
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 指定閉分母上の元の Hom の実屋根への包含は、実商比較と全次数で厳密に可換。 -/
lemma dgClosedRoofHomInclusion_comparison (P : Set D) (x y : D)
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion A D P x y s ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((DGQuotient.inclusion A D P).map
        (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s.obj.left) y) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientClosedRoofHomInclusion A D P x y s := by
  apply pullback.hom_ext
  · have h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceTarget A D P x y =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceTarget A D P x y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientTargetSliceMap A D P y :=
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap_target A D P x y
    calc
      _ = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion A D P x y s ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceTarget A D P x y) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientTargetSliceMap A D P y :=
        (Category.assoc _ _ _).trans
          ((congrArg (fun f => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion A D P x y s ≫ f) h).trans
            (Category.assoc _ _ _).symm)
      _ = _ := congrArg (fun f => f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientTargetSliceMap A D P y)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion_target A D P x y s)
      _ = _ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientTargetSliceMap_pinched A D P
        (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s.obj.left) y
      _ = _ := congrArg (fun f => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((DGQuotient.inclusion A D P).map
        (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s.obj.left) y) ≫ f)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientClosedRoofHomInclusion_target A D P x y s).symm
      _ = _ := (Category.assoc _ _ _).symm
  · change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion A D P x y s ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceProjection A D P x y =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((DGQuotient.inclusion A D P).map
        (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s.obj.left) y) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientClosedRoofHomInclusion A D P x y s) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceProjection A D P x y
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap_projection,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion_projection, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientClosedRoofHomInclusion_projection, SSet.comp_const]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
