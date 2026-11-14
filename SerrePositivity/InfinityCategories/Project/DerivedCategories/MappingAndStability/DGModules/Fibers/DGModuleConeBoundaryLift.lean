module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleConeHomDifferential
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleHomPrecompose

/-! # dg 加群の cone 境界の二成分からの原始元

概要：二つの境界成分に共通の符号を掛けて指定残差の原始元を構成する。
方針：cone Hom 座標の逆と行列微分を使い、二つの整合条件を代入する。
規約：境界から整合条件を回収する部分は別工程。使われ方：β3 の cofiber の実境界充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N X : ModuleCategory A D}

/-- cone の後続未知成分を二つの境界成分から明示的に構成。 -/
def dgModuleConeBoundaryLift (f : M ⟶ N) (n : ℤ)
    (a : GradedHom A (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) X) n)
    (b : GradedHom A (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) X) (n + 1)) :
    GradedHom A (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (ForgetEnrichment.to (Complex A) X) (n + 1) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeHomCoordinates A D f n).symm (n.negOnePow • a, n.negOnePow • b)

/-- 明示的な原始元候補の二座標は指定成分の共通の符号倍。 -/
lemma dgModuleConeBoundaryLift_coordinates (f : M ⟶ N) (n : ℤ) (a) (b) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeHomCoordinates A D f n (dgModuleConeBoundaryLift A D (X := X) f n a b) =
      (n.negOnePow • a, n.negOnePow • b) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeHomCoordinates A D f n).apply_symm_apply _

/-- 線形残差の二つの整合条件から実際の原始元を得る。 -/
lemma dgModuleConeBoundaryLift_differential (f : M ⟶ N) (n : ℤ)
    (a : GradedHom A (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) X) n)
    (b : GradedHom A (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) X) (n + 1))
    (r : GradedHom A (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (ForgetEnrichment.to (Complex A) X) (n + 1 + 1))
    (ha : differential A a = n.negOnePow •
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeHomCoordinates A D f (n + 1) r).1 -
        (show GradedHom A (ForgetEnrichment.to (Complex A) M)
          (ForgetEnrichment.to (Complex A) X) (n + 1) from
          (eHomWhiskerRight (Complex A) f X).f (n + 1) b)))
    (hb : differential A b = n.negOnePow • (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeHomCoordinates A D f (n + 1) r).2) :
    differential A (dgModuleConeBoundaryLift A D f n a b) = r := by
  have hε : (n + 1 + 1).negOnePow = n.negOnePow := by
    simp only [Int.negOnePow_succ, neg_neg]
  have hsmul {Y Z : RightModule A D} (k : ℤ) (z : GradedHom A Y Z k) :
      differential A (n.negOnePow • z) = n.negOnePow • differential A z := by
    simp only [differential, Units.smul_def, map_zsmul]
  rw [dgModuleConeBoundaryLift, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeHomCoordinates_symm_differential,
    ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHom_precompose_eq_compose A D f (n + 1), hε,
    hsmul, hsmul, ha, hb]
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeHomCoordinates A D f (n + 1)).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Prod.ext
  · simp only [Units.smul_def, map_zsmul]
    simp only [← Units.smul_def, smul_sub, smul_smul, Int.units_mul_self,
      one_smul, sub_add_cancel]
  · simp only [smul_smul, Int.units_mul_self, one_smul]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
