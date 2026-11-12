module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.RepresentableModel
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ActionElements

/-! 代表加群表示の augmentation を全整数次数で元の閉元の作用に同定する。 -/
@[expose] public section
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories Opposite
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
lemma dgGluingAugmentation_unit (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    ((moduleEvaluation R C X.left).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M X)).f 0
      (unitElement R X.left).val = X.gluing.val := by
  have h := congrArg (fun f ↦ (cycleFromUnit _ f).val)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation_value R C D M X)
  rw [cycleFromUnit_postcomp] at h
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject.gluingMap, cycleFromUnit_unitFromCycle] at h
  change (dgYonedaIso R X.left (M.rightAt X.right)).hom.f 0
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M X))).val = X.gluing.val at h
  dsimp only [dgYonedaIso] at h
  rw [yonedaEvaluateFamily_apply] at h
  change (Cochain.ofHom ((moduleEvaluation R C X.left).map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M X))).v 0 0 (add_zero 0) (unitElement R X.left).val = _
  rw [moduleEvaluation_cochain R C X.left (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M X)]
  exact h


lemma dgGluingAugmentation_apply (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) (c : C)
    (n : ℤ) (f : GradedHom R c X.left n) :
    ((moduleEvaluation R C c).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M X)).f n f =
      moduleAction R (M.rightAt X.right) (x := op X.left) (y := op c)
        f X.gluing.val (zero_add n) := by
  change (Cochain.ofHom ((moduleEvaluation R C c).map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M X))).v n n (add_zero n) f = _
  rw [moduleEvaluation_cochain]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation, ForgetEnrichment.homTo_homOf,
    cycleFromUnit_postcomp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject.gluingMap, cycleFromUnit_unitFromCycle]
  change (((dgYonedaIso R X.left (M.rightAt X.right)).inv ≫
    moduleHomπ R C (representable R X.left) (M.rightAt X.right) c).f 0
      X.gluing.val).v n n (add_zero n) f = _
  change (((moduleHomEquiv R C (M.value X.left X.right)
    (representable R X.left) (M.rightAt X.right)).symm
      (yonedaExtension R X.left (M.rightAt X.right) (𝟙 _)) ≫
    moduleHomπ R C (representable R X.left) (M.rightAt X.right) c).f 0
      X.gluing.val).v n n (add_zero n) f = _
  rw [moduleHomEquiv_symm_π]
  change ((yonedaExtensionApp R X.left (M.rightAt X.right) (𝟙 _) (op c)).f 0
    X.gluing.val).v n n (add_zero n) f = _
  rw [yonedaExtensionApp_apply]
  simp


end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
