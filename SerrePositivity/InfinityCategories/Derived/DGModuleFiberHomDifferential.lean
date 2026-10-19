module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberHomInverse
public import SerrePositivity.InfinityCategories.Derived.DGModuleConeLiftDifferential

/-! # shifted cone への全 Hom の行列微分

概要：fiber の逆座標の微分を (da, f a − db) と同定する。
方針：cone lift の微分と shift の反可換性を合成して符号を整理する。
規約：第二座標は nullhomotopy との合成。使われ方：β3 の実境界の原始元。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {T M N : ModuleCategory A D}

/-- cone lift の両成分の符号反転は全体の符号反転。 -/
lemma dgModuleConeLiftElement_neg (f : M ⟶ N) (n : ℤ) (a) (b) :
    -moduleConeLiftElement A D (T := T) f n a b =
      moduleConeLiftElement A D f n (-a) (-b) := by
  have h : -complexConeElementMk A (eHomWhiskerLeft (Complex A) T f) n a b =
      complexConeElementMk A (eHomWhiskerLeft (Complex A) T f) n (-a) (-b) := by
    apply complexConeElement_ext A _ n <;>
      simp only [map_neg, complexConeElementMk_fst, complexConeElementMk_snd]
  change -((moduleHomConeComparison A D T f).f n).hom _ =
    ((moduleHomConeComparison A D T f).f n).hom _
  rw [← map_neg, h]

/-- fiber の逆座標は微分 (da, f a − db) と可換。 -/
lemma dgModuleFiberHomCoordinates_symm_differential (f : M ⟶ N) (n : ℤ)
    (a : GradedHom A (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) M) (n + 1))
    (b : GradedHom A (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) N) n) :
    differential A ((dgModuleFiberHomCoordinates A D T f n).symm (a, b)) =
      (dgModuleFiberHomCoordinates A D T f (n + 1)).symm
        (differential A a, compose A
          (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val a (add_zero (n + 1)) -
            differential A b) := by
  rw [dgModuleFiberHomCoordinates_symm, dgModuleFiberHomCoordinates_symm,
    dgModuleNegativeShiftTargetHomEquiv_symm_differential]
  have h := dgModuleConeLiftElement_differential A D f n a (-b)
  change differential (D := RightModule A D) A (moduleConeLiftElement A D f n a (-b)) = _ at h
  rw [h, ← map_neg, dgModuleConeLiftElement_neg, neg_neg]
  have hb : differential (D := RightModule A D) A (-b) = -differential A b := map_neg _ _
  congr 2
  rw [hb]
  abel

end SerrePositivity.InfinityCategories
