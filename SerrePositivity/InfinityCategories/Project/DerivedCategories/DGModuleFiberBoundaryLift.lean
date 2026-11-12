module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFiberHomDifferential
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFiberHomProjections

/-! # fiber の二残差からの全 Hom end 内の原始元

概要：脚と三角形の残差から fiber への未知先頭成分を定義する。
方針：二残差の負を逆座標へ入れ、行列微分に整合条件を代入する。
規約：実境界からの整合条件の導出は別工程。使われ方：β3 の実 slice 境界充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {T M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- fiber の未知先頭成分を二残差から明示的に構成。 -/
def dgModuleFiberBoundaryLift (f : M ⟶ N) (n : ℤ)
    (a : _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) T)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M) (n + 1))
    (b : _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) T)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N) n) :
    GradedHom A (ForgetEnrichment.to (Complex A) T) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f) (n + 1) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberHomCoordinates A D T f n).symm (-a, -b)

/-- 明示解の射影との合成は指定した第一残差の負。 -/
lemma dgModuleFiberBoundaryLift_projection (f : M ⟶ N) (n : ℤ) (a) (b) :
    compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjectionElement A D f)
      (dgModuleFiberBoundaryLift A D (T := T) f n a b) (add_zero (n + 1)) = -a :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberHomCoordinates_symm_projection A D f n (-a) (-b)

/-- 明示解の零ホモトピーとの合成は指定した第二残差の負。 -/
lemma dgModuleFiberBoundaryLift_nullHomotopy (f : M ⟶ N) (n : ℤ) (a) (b) :
    compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy A D f)
      (dgModuleFiberBoundaryLift A D (T := T) f n a b) (by omega) = -b :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberHomCoordinates_symm_nullHomotopy A D f n (-a) (-b)

/-- 実射影・零ホモトピーに沿う残差の整合条件から原始元を得る。 -/
lemma dgModuleFiberBoundaryLift_differential (f : M ⟶ N) (n : ℤ)
    (a : _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) T)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M) (n + 1))
    (b : _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) T)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N) n)
    (r : _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) T)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f) (n + 1 + 1))
    (ha : _root_.SerrePositivity.DifferentialGraded.differential A a =
      -compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjectionElement A D f) r (add_zero (n + 1 + 1)))
    (hb : _root_.SerrePositivity.DifferentialGraded.differential A b = _root_.SerrePositivity.DifferentialGraded.compose A
      (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) f)).val a (add_zero (n + 1)) +
        compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy A D f) r (by omega)) :
    _root_.SerrePositivity.DifferentialGraded.differential A (dgModuleFiberBoundaryLift A D f n a b) = r := by
  have hda : _root_.SerrePositivity.DifferentialGraded.differential (D := _root_.SerrePositivity.DifferentialGraded.RightModule A D) A (-a) = -differential A a := map_neg _ _
  have hdb : _root_.SerrePositivity.DifferentialGraded.differential (D := _root_.SerrePositivity.DifferentialGraded.RightModule A D) A (-b) = -differential A b := map_neg _ _
  have hcomp := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sub_right (A := A)
    (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) f)).val
    (0 : _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) T)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M) (n + 1)) a (add_zero (n + 1))
  simp only [zero_sub, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero] at hcomp
  rw [dgModuleFiberBoundaryLift, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberHomCoordinates_symm_differential,
    hda, hdb, hcomp, ha, hb, neg_neg]
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberHomCoordinates A D T f (n + 1)).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Prod.ext
  · simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberHomCoordinates_fst]
  · simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberHomCoordinates_snd]
    abel

end SerrePositivity.InfinityCategories.Project.DerivedCategories
