module
public import SerrePositivity.DifferentialGraded.Quotient.AppendErasureRecursion

/-! # 左有限pathを固定した連結のε消去Leibniz則 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 全右pathへの連結に対する、左右のε消去のLeibniz則。 -/
lemma appendRight_erasure {S : Set D} (w : Word S) (x y z : D) :
    (Cochain.ofHom (appendRight A D w x y z)).comp (erasure A D S x z) (zero_add 1) =
    ((tensorRightHom (internalHom A D S y z) (term A D w x y)
      (internalHom A D S x y)).f 1 (eraseRow A D w x y)).comp
      (Cochain.ofHom (internalComposition A D S x y z)) (add_zero 1) +
    ((tensorLeftHom (term A D w x y) (internalHom A D S y z)
      (internalHom A D S y z)).f 1 (erasure A D S y z)).comp
      (Cochain.ofHom (appendRight A D w x y z)) (add_zero 1) := by
  induction w generalizing x with
  | nil =>
    rw [appendRight_nil, eraseRow_nil, map_zero, Cochain.zero_comp, zero_add]
    exact internalPrepend_erasure A D S x y z
  | cons b w ih =>
    rw [appendRight_erasure_cons, ih b.val, appendLiftCochain_add,
      ← appendLiftCochain_left, ← appendLiftCochain_right, eraseRow_cons, map_add]
    rw [Cochain.add_comp _ _ _ (add_zero 1)]
    rw [tensorRightHom_cochain_comp, tensorRightHom_ofHom,
      Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp,
      internalComposition_left_ι]
    exact (add_assoc _ _ _).symm

end SerrePositivity.DifferentialGraded.DGQuotient
