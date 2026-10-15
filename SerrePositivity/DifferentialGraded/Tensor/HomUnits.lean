module
public import SerrePositivity.DifferentialGraded.Tensor.HomElements
public import SerrePositivity.DifferentialGraded.Functor.Components
public import SerrePositivity.DifferentialGraded.Bimodule.UncurryHom

/-! # balanced tensorの主Hom写像の単位保存 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleHom_unit_π (M : RightModule A D) (x : D) :
    (moduleHomπ A D M M x).f 0 (unitElement A M).val = Cochain.ofHom (𝟙 (M.obj (op x))) := by
  have h := DGFunctor.map_unitElement A (moduleEvaluationDG A D x) M
  rw [Bimodule.complex_unitElement] at h
  exact h

lemma leftModuleHom_unit_π (N : LeftModule A D) (x : D) :
    (leftModuleHomπ A D N N x).f 0 (unitElement A N).val = Cochain.ofHom (𝟙 (N.obj x)) := by
  have h := DGFunctor.map_unitElement A (leftModuleEvaluationDG A D x) N
  rw [Bimodule.complex_unitElement] at h
  exact h

lemma rightHomMap_unit (M : RightModule A D) (N : LeftModule A D) :
    (rightHomMap A D M M N).f 0 (unitElement A M).val =
      (unitElement A (obj A D M N)).val := by
  rw [Bimodule.complex_unitElement]
  apply cochain_zero_element_ext A D M N
  intro x r s a ha m v
  rw [rightHomMap_element_of_sum A D N _ x m v ha (zero_add r) (add_zero a),
    moduleHom_unit_π]
  simp only [Cochain.ofHom_v, HomologicalComplex.id_f, ModuleCat.id_apply]

lemma leftHomMap_unit (M : RightModule A D) (N : LeftModule A D) :
    (leftHomMap A D M N N).f 0 (unitElement A N).val =
      (unitElement A (obj A D M N)).val := by
  rw [Bimodule.complex_unitElement]
  apply cochain_zero_element_ext A D M N
  intro x r s a ha m v
  rw [leftHomMap_element_of_sum A D M _ x m v ha (zero_add s) (add_zero a),
    leftModuleHom_unit_π]
  simp only [zero_mul, Int.negOnePow_zero, one_smul, Cochain.ofHom_v,
    HomologicalComplex.id_f, ModuleCat.id_apply]

end SerrePositivity.DifferentialGraded.BalancedTensor
