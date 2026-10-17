module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.GeneratorBoundary

/-! # cell生成元が与えるdiskと指定境界の可換square -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (I : Type w) [Small.{u} I] (C : Family A D I)

/-- 追加した生成元とその微分を持つ実際のdisk射。 -/
def generatorDisk (i : I) :
    complexDisk A (C.degree i) ⟶ C.attachedHom A D I (C.source i) (C.target i) :=
  (complexDiskHomEquiv A _ (C.degree i)).symm (C.generatorElement A D I i)

lemma generatorDisk_generator (i : I) :
    complexDiskHomEquiv A (C.attachedHom A D I (C.source i) (C.target i))
      (C.degree i) (C.generatorDisk A D I i) = C.generatorElement A D I i :=
  (complexDiskHomEquiv A _ (C.degree i)).apply_symm_apply _

/-- sphere境界を元のHomへ入れる射は、付加したdiskを通る。 -/
lemma generatorDisk_boundary (i : I) :
    complexSphereToDisk A (C.degree i) ≫ C.generatorDisk A D I i =
    complexSphereMap A (C.degree i + 1) (C.boundary i) ≫
      C.originalHomInclusion A D I (C.source i) (C.target i) := by
  apply (complexSphereHomEquiv A _ (C.degree i + 1)).injective
  apply Subtype.ext
  rw [complexSphereToDisk_comp, generatorDisk_generator, differential_generatorElement]
  change _ = (complexSphereCycle A (C.degree i + 1)
    (complexSphereMap A (C.degree i + 1) (C.boundary i) ≫
      C.originalHomInclusion A D I (C.source i) (C.target i))).val
  rw [complexSphereCycle_comp]
  have h : (complexSphereCycle A (C.degree i + 1)
      (complexSphereMap A (C.degree i + 1) (C.boundary i))).val = (C.boundary i).val :=
    congrArg Subtype.val ((complexSphereHomEquiv A _ (C.degree i + 1)).apply_symm_apply _)
  rw [h]

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
