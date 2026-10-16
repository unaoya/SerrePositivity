module
public import SerrePositivity.DifferentialGraded.Quotient.AppendErasure
public import SerrePositivity.DifferentialGraded.Quotient.TensorRightPathCochainExt

/-! # 全path合成のε消去Leibniz則 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 全path直和の内部合成はε消去作用素に関してもLeibniz則を満たす。 -/
lemma internalComposition_erasure (S : Set D) (x y z : D) :
    (Cochain.ofHom (internalComposition A D S x y z)).comp (erasure A D S x z)
      (zero_add 1) =
    ((tensorRightHom (internalHom A D S y z) (internalHom A D S x y)
      (internalHom A D S x y)).f 1 (erasure A D S x y)).comp
      (Cochain.ofHom (internalComposition A D S x y z)) (add_zero 1) +
    ((tensorLeftHom (internalHom A D S x y) (internalHom A D S y z)
      (internalHom A D S y z)).f 1 (erasure A D S y z)).comp
      (Cochain.ofHom (internalComposition A D S x y z)) (add_zero 1) := by
  apply tensorRightPathCochain_ext A D S x y (internalHom A D S y z) 1
  intro w
  have hl : (Cochain.ofHom (ι A D S x y w ▷ internalHom A D S y z)).comp
      ((tensorRightHom (internalHom A D S y z) (internalHom A D S x y)
        (internalHom A D S x y)).f 1 (erasure A D S x y)) (zero_add 1) =
      (tensorRightHom (internalHom A D S y z) (term A D w x y)
        (internalHom A D S x y)).f 1 (eraseRow A D w x y) := by
    rw [← tensorRightHom_ofHom, ← tensorRightHom_cochain_comp, erasure_precomp]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    internalComposition_left_ι]
  rw [Cochain.comp_add _ _ _ (zero_add 1),
    ← Cochain.comp_assoc_of_first_is_zero_cochain, hl,
    ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← tensorLeftHom_cochain_naturality,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp,
    internalComposition_left_ι]
  exact appendRight_erasure A D w x y z

end SerrePositivity.DifferentialGraded.DGQuotient
