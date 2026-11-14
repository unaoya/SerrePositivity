module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.KernelCone

/-! tensor–Yoneda の列比較の全次数での自然性。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)

/-- 列比較の実射は、全 Hom に自然な tensor 右単位の実射そのもの。 -/
lemma dgGluingKernelColumnIso_hom_unit (d : D) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) d)).hom =
    (BimoduleTensor.rightUnitIso R C D M d).hom := by
  simp [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelColumnIso, Morita.criterionPerfYonedaTensorIso]
  rfl

/-- Yoneda を通常 kernel tensor に続けた全 Hom は合成双加群の全 Hom と一致。 -/
lemma dgGluingKernelYoneda_map (d d' : D) :
    yonedaHom R D d d' ≫ (Morita.kernelTensor R D C M).map
      (representable R d) (representable R d') =
    (BimoduleTensor.compose R C D D M (Bimodule.diagonal R D)).toFunctor.map d d' := by
  apply moduleHom_ext R C
  intro c
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => (dgYoneda R D).map d d' ≫ k)
      (Morita.kernelTensor_map_π R D C M (representable R d) (representable R d') c)).trans
        (BimoduleTensor.compose_leftMap_π R C D D M (Bimodule.diagonal R D) d d' c).symm)

/-- tensor–Yoneda の列比較は閉零射だけでなく全整数次数の Hom に自然。 -/
lemma dgGluingKernelColumnIso_hom_naturality (d d' : D) :
    yonedaHom R D d d' ≫ (Morita.kernelTensor R D C M).map
      (representable R d) (representable R d') ≫
      eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R)
          ((Morita.kernelTensor R D C M).obj (representable R d)))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) d')).hom =
    M.toFunctor.map d d' ≫ eHomWhiskerRight (Complex R)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) d)).hom
      (ForgetEnrichment.of (Complex R) (M.rightAt d')) := by
  rw [← Category.assoc, dgGluingKernelYoneda_map,
    dgGluingKernelColumnIso_hom_unit, dgGluingKernelColumnIso_hom_unit]
  exact BimoduleTensor.rightUnitIso_naturality R C D M d d'

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
