module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.BoundaryRowRecursion
public import SerrePositivity.DifferentialGraded.Resolution.Cells.InternalBoundaryHead

/-! # 先頭cell追加に対する全境界置換作用素の再帰式 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

lemma prefixPath_replacement (b : I) (x y : D) :
    (Cochain.ofHom (C.prefixPath A D I b x y)).comp (C.replacement A D I x y) (zero_add 1) =
    C.internalReplaceFirst A D I b x y +
    ((tensorLeftHom (homObject A D x (C.source b)) _ _).f 1
      ((tensorLeftHom (C.generator A D I b) _ _).f 1
        (C.replacement A D I (C.target b) y))).comp
      (Cochain.ofHom (C.prefixPath A D I b x y)) (add_zero 1) := by
  apply C.prefixPathCochain_ext A D I b x y 1
  intro w
  have ht : (Cochain.ofHom ((homObject A D x (C.source b)) ◁
      ((C.generator A D I b) ◁ C.inclusion A D I w (C.target b) y))).comp
      ((tensorLeftHom (homObject A D x (C.source b)) _ _).f 1
        ((tensorLeftHom (C.generator A D I b) _ _).f 1
          (C.replacement A D I (C.target b) y))) (zero_add 1) =
    (tensorLeftHom (homObject A D x (C.source b)) _ _).f 1
      ((tensorLeftHom (C.generator A D I b) _ _).f 1
        (C.replaceRow A D I w (C.target b) y)) := by
    rw [← tensorLeftHom_ofHom (homObject A D x (C.source b)),
      ← tensorLeftHom_cochain_comp, ← tensorLeftHom_ofHom (C.generator A D I b),
      ← tensorLeftHom_cochain_comp, replacement_precomp]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    prefixPath_inclusion, replacement_precomp, Cochain.comp_add,
    internalReplaceFirst_inclusion, ← Cochain.comp_assoc_of_first_is_zero_cochain, ht]
  exact C.replaceRow_cons A D I b w x y

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
