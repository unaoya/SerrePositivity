module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleFiberHomInverse
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleConeLiftDifferential

/-! # shifted cone への全 Hom の行列微分

概要：fiber の逆座標の微分を (da, f a − db) と同定する。
方針：cone lift の微分と shift の反可換性を合成して符号を整理する。
規約：第二座標は nullhomotopy との合成。使われ方：β3 の実境界の原始元。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {T M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- cone lift の両成分の符号反転は全体の符号反転。 -/
lemma dgModuleConeLiftElement_neg (f : M ⟶ N) (n : ℤ) (a) (b) :
    -_root_.SerrePositivity.DifferentialGraded.moduleConeLiftElement A D (T := T) f n a b =
      _root_.SerrePositivity.DifferentialGraded.moduleConeLiftElement A D f n (-a) (-b) := by
  have h : -_root_.SerrePositivity.DifferentialGraded.complexConeElementMk A (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex A) T f) n a b =
      _root_.SerrePositivity.DifferentialGraded.complexConeElementMk A (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex A) T f) n (-a) (-b) := by
    apply _root_.SerrePositivity.DifferentialGraded.complexConeElement_ext A _ n <;>
      simp only [map_neg, _root_.SerrePositivity.DifferentialGraded.complexConeElementMk_fst, _root_.SerrePositivity.DifferentialGraded.complexConeElementMk_snd]
  change -((_root_.SerrePositivity.DifferentialGraded.moduleHomConeComparison A D T f).f n).hom _ =
    ((_root_.SerrePositivity.DifferentialGraded.moduleHomConeComparison A D T f).f n).hom _
  rw [← map_neg, h]

/-- fiber の逆座標は微分 (da, f a − db) と可換。 -/
lemma dgModuleFiberHomCoordinates_symm_differential (f : M ⟶ N) (n : ℤ)
    (a : _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) T)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M) (n + 1))
    (b : _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) T)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N) n) :
    differential A ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberHomCoordinates A D T f n).symm (a, b)) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberHomCoordinates A D T f (n + 1)).symm
        (_root_.SerrePositivity.DifferentialGraded.differential A a, _root_.SerrePositivity.DifferentialGraded.compose A
          (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) f)).val a (add_zero (n + 1)) -
            _root_.SerrePositivity.DifferentialGraded.differential A b) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberHomCoordinates_symm, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberHomCoordinates_symm,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNegativeShiftTargetHomEquiv_symm_differential]
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeLiftElement_differential A D f n a (-b)
  change _root_.SerrePositivity.DifferentialGraded.differential (D := _root_.SerrePositivity.DifferentialGraded.RightModule A D) A (_root_.SerrePositivity.DifferentialGraded.moduleConeLiftElement A D f n a (-b)) = _ at h
  rw [h, ← map_neg, dgModuleConeLiftElement_neg, neg_neg]
  have hb : _root_.SerrePositivity.DifferentialGraded.differential (D := _root_.SerrePositivity.DifferentialGraded.RightModule A D) A (-b) = -differential A b := map_neg _ _
  congr 2
  rw [hb]
  abel

end SerrePositivity.InfinityCategories.Project.DerivedCategories
