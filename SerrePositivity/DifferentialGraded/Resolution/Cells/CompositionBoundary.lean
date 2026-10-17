module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.AppendBoundary
public import SerrePositivity.DifferentialGraded.Resolution.Cells.TensorRightPathCochainExt

/-! # 任意次数cellの全合成の微分整合性：CompositionBoundary -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits Preadditive MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

/-- 全path直和の内部合成は境界置換作用素に関してもLeibniz則を満たす。 -/
lemma internalComposition_replacement (x y z : D) :
    (Cochain.ofHom (C.internalComposition A D I x y z)).comp (C.replacement A D I x z)
      (zero_add 1) =
    ((tensorRightHom (C.internalHom A D I y z) (C.internalHom A D I x y)
      (C.internalHom A D I x y)).f 1 (C.replacement A D I x y)).comp
      (Cochain.ofHom (C.internalComposition A D I x y z)) (add_zero 1) +
    ((tensorLeftHom (C.internalHom A D I x y) (C.internalHom A D I y z)
      (C.internalHom A D I y z)).f 1 (C.replacement A D I y z)).comp
      (Cochain.ofHom (C.internalComposition A D I x y z)) (add_zero 1) := by
  apply C.tensorRightPathCochain_ext A D I x y (C.internalHom A D I y z) 1
  intro w
  have hl : (Cochain.ofHom (C.inclusion A D I w x y ▷ C.internalHom A D I y z)).comp
      ((tensorRightHom (C.internalHom A D I y z) (C.internalHom A D I x y)
        (C.internalHom A D I x y)).f 1 (C.replacement A D I x y)) (zero_add 1) =
      (tensorRightHom (C.internalHom A D I y z) (C.term A D I w x y)
        (C.internalHom A D I x y)).f 1 (C.replaceRow A D I w x y) := by
    rw [← tensorRightHom_ofHom, ← tensorRightHom_cochain_comp, replacement_precomp]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    internalComposition_left_inclusion]
  rw [Cochain.comp_add _ _ _ (zero_add 1),
    ← Cochain.comp_assoc_of_first_is_zero_cochain, hl,
    ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← tensorLeftHom_cochain_naturality,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp,
    internalComposition_left_inclusion]
  exact C.appendRight_replacement A D I w x y z

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
