module
public import SerrePositivity.DifferentialGraded.Tensor.GradedSplitElements

/-! # balanced tensor後の次数付き分裂の恒等式 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Limits Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N P : ModuleCategory A D} {f : M ⟶ N} {g : N ⟶ P}

lemma tensor_inclusion_retraction (s : ModuleGradedSplit A D f g) (L : LeftModule A D) :
    (Cochain.ofHom (rightTensorMap A D L f)).comp
      (tensorRetractionCochain A D s L) (zero_add 0) =
      Cochain.ofHom (𝟙 (obj A D (ForgetEnrichment.to (Complex A) M) L)) := by
  apply cochain_zero_element_ext A D (ForgetEnrichment.to (Complex A) M) L
  intro x r t a ha m v
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ModuleCat.comp_apply]
  rw [rightTensorMap_element A D L f x m v ha,
    tensorRetractionCochain_element A D s L x ha _ v]
  have h := congrArg (fun k => k m) (s.inclusion_retraction x r)
  change s.retraction x r (((moduleEvaluation A D x).map f).f r m) = m at h
  rw [h]
  rfl

lemma tensor_section_projection (s : ModuleGradedSplit A D f g) (L : LeftModule A D) :
    (tensorSectionCochain A D s L).comp
      (Cochain.ofHom (rightTensorMap A D L g)) (add_zero 0) =
      Cochain.ofHom (𝟙 (obj A D (ForgetEnrichment.to (Complex A) P) L)) := by
  apply cochain_zero_element_ext A D (ForgetEnrichment.to (Complex A) P) L
  intro x r t a ha m v
  simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, ModuleCat.comp_apply]
  rw [tensorSectionCochain_element A D s L x ha m v,
    rightTensorMap_element A D L g x (s.section_ x r m) v ha]
  have h := congrArg (fun k => k m) (s.section_projection x r)
  change ((moduleEvaluation A D x).map g).f r (s.section_ x r m) = m at h
  rw [h]
  rfl

lemma element_add_left (M : RightModule A D) (L : LeftModule A D) (x : D)
    {r t a : ℤ} (ha : r + t = a) (m m' : (M.obj (op x)).X r) (v : (L.obj x).X t) :
    element A D M L x (m + m') v ha =
      element A D M L x m v ha + element A D M L x m' v ha := by
  simp only [element, TensorProduct.add_tmul, map_add]

lemma tensor_decomposition (s : ModuleGradedSplit A D f g) (L : LeftModule A D) :
    (tensorRetractionCochain A D s L).comp
        (Cochain.ofHom (rightTensorMap A D L f)) (add_zero 0) +
      (Cochain.ofHom (rightTensorMap A D L g)).comp
        (tensorSectionCochain A D s L) (zero_add 0) =
      Cochain.ofHom (𝟙 (obj A D (ForgetEnrichment.to (Complex A) N) L)) := by
  apply cochain_zero_element_ext A D (ForgetEnrichment.to (Complex A) N) L
  intro x r t a ha m v
  simp only [Cochain.add_v, Cochain.comp_zero_cochain_v,
    Cochain.ofHom_v, ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.comp_apply]
  rw [tensorRetractionCochain_element A D s L x ha m v,
    rightTensorMap_element A D L f x (s.retraction x r m) v ha,
    rightTensorMap_element A D L g x m v ha,
    tensorSectionCochain_element A D s L x ha _ v, ← element_add_left]
  have h := congrArg (fun k => k m) (s.decomposition x r)
  change ((moduleEvaluation A D x).map f).f r (s.retraction x r m) +
    s.section_ x r (((moduleEvaluation A D x).map g).f r m) = m at h
  rw [h]
  rfl

end SerrePositivity.DifferentialGraded.BalancedTensor
