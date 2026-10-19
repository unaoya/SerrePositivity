module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberHomDifferential
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberHomProjections

/-! # fiber の二残差からの全 Hom end 内の原始元

概要：脚と三角形の残差から fiber への未知先頭成分を定義する。
方針：二残差の負を逆座標へ入れ、行列微分に整合条件を代入する。
規約：実境界からの整合条件の導出は別工程。使われ方：β3 の実 slice 境界充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {T M N : ModuleCategory A D}

/-- fiber の未知先頭成分を二残差から明示的に構成。 -/
def dgModuleFiberBoundaryLift (f : M ⟶ N) (n : ℤ)
    (a : GradedHom A (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) M) (n + 1))
    (b : GradedHom A (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) N) n) :
    GradedHom A (ForgetEnrichment.to (Complex A) T) (dgModuleFiber A D f) (n + 1) :=
  (dgModuleFiberHomCoordinates A D T f n).symm (-a, -b)

/-- 明示解の射影との合成は指定した第一残差の負。 -/
lemma dgModuleFiberBoundaryLift_projection (f : M ⟶ N) (n : ℤ) (a) (b) :
    compose A (dgModuleFiberProjectionElement A D f)
      (dgModuleFiberBoundaryLift A D (T := T) f n a b) (add_zero (n + 1)) = -a :=
  dgModuleFiberHomCoordinates_symm_projection A D f n (-a) (-b)

/-- 明示解の零ホモトピーとの合成は指定した第二残差の負。 -/
lemma dgModuleFiberBoundaryLift_nullHomotopy (f : M ⟶ N) (n : ℤ) (a) (b) :
    compose A (dgModuleFiberNullHomotopy A D f)
      (dgModuleFiberBoundaryLift A D (T := T) f n a b) (by omega) = -b :=
  dgModuleFiberHomCoordinates_symm_nullHomotopy A D f n (-a) (-b)

/-- 実射影・零ホモトピーに沿う残差の整合条件から原始元を得る。 -/
lemma dgModuleFiberBoundaryLift_differential (f : M ⟶ N) (n : ℤ)
    (a : GradedHom A (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) M) (n + 1))
    (b : GradedHom A (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) N) n)
    (r : GradedHom A (ForgetEnrichment.to (Complex A) T)
      (dgModuleFiber A D f) (n + 1 + 1))
    (ha : differential A a =
      -compose A (dgModuleFiberProjectionElement A D f) r (add_zero (n + 1 + 1)))
    (hb : differential A b = compose A
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val a (add_zero (n + 1)) +
        compose A (dgModuleFiberNullHomotopy A D f) r (by omega)) :
    differential A (dgModuleFiberBoundaryLift A D f n a b) = r := by
  have hda : differential (D := RightModule A D) A (-a) = -differential A a := map_neg _ _
  have hdb : differential (D := RightModule A D) A (-b) = -differential A b := map_neg _ _
  have hcomp := compose_sub_right (A := A)
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val
    (0 : GradedHom A (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) M) (n + 1)) a (add_zero (n + 1))
  simp only [zero_sub, compose_zero] at hcomp
  rw [dgModuleFiberBoundaryLift, dgModuleFiberHomCoordinates_symm_differential,
    hda, hdb, hcomp, ha, hb, neg_neg]
  apply (dgModuleFiberHomCoordinates A D T f (n + 1)).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Prod.ext
  · simp only [dgModuleFiberHomCoordinates_fst]
  · simp only [dgModuleFiberHomCoordinates_snd]
    abel

end SerrePositivity.InfinityCategories
