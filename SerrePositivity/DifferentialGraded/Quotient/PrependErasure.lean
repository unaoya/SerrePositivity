module
public import SerrePositivity.DifferentialGraded.Quotient.PrependErasureRows
public import SerrePositivity.DifferentialGraded.Quotient.ErasureOperator
public import SerrePositivity.DifferentialGraded.Quotient.TensorPathCochainExt

/-! # 全path直和における先頭Hom作用とε消去の可換性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 空pathを左に置く合成のε消去Leibniz則。左の元のHomには消去項がない。 -/
lemma internalPrepend_erasure (S : Set D) (x y z : D) :
    (Cochain.ofHom (internalPrepend A D S x y z)).comp (erasure A D S x z) (zero_add 1) =
    ((tensorLeftHom (homObject A D x y) (internalHom A D S y z)
      (internalHom A D S y z)).f 1 (erasure A D S y z)).comp
      (Cochain.ofHom (internalPrepend A D S x y z)) (add_zero 1) := by
  apply tensorLeftPathCochain_ext A D S y z (homObject A D x y) 1
  intro w
  have hb : (Cochain.ofHom ((homObject A D x y) ◁ ι A D S y z w)).comp
      ((tensorLeftHom (homObject A D x y) (internalHom A D S y z)
        (internalHom A D S y z)).f 1 (erasure A D S y z)) (zero_add 1) =
      (tensorLeftHom (homObject A D x y) (term A D w y z)
        (internalHom A D S y z)).f 1 (eraseRow A D w y z) := by
    rw [← tensorLeftHom_ofHom, ← tensorLeftHom_cochain_comp, erasure_precomp]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    internalPrepend_ι, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    erasure_precomp, ← Cochain.comp_assoc_of_first_is_zero_cochain, hb]
  exact prependMap_eraseRow A D w x y z

/-- 空pathを左に置く消去Leibniz則の斉次成分。右側の消去には(-1)^pが付く。 -/
lemma internalPrepend_erasure_apply (S : Set D) (x y z : D) (p q n : ℤ)
    (hn : p + q = n) (a : (homObject A D x y).X p) (b : (internalHom A D S y z).X q) :
    (erasure A D S x z).v n (n + 1) rfl
      ((internalPrepend A D S x y z).f n
        (ιTensorObj (homObject A D x y) (internalHom A D S y z) p q n hn (a ⊗ₜ[A] b))) =
    p.negOnePow • (internalPrepend A D S x y z).f (n + 1)
      (ιTensorObj (homObject A D x y) (internalHom A D S y z) p (q + 1) (n + 1)
        (by omega) (a ⊗ₜ[A] (erasure A D S y z).v q (q + 1) rfl b)) := by
  have h := congrArg (fun f : Cochain
      (homObject A D x y ⊗ internalHom A D S y z) (internalHom A D S x z) 1 =>
    f.v n (n + 1) rfl
      (ιTensorObj (homObject A D x y) (internalHom A D S y z) p q n hn (a ⊗ₜ[A] b)))
    (internalPrepend_erasure A D S x y z)
  rw [cochain_ofHom_comp_apply, cochain_comp_ofHom_apply,
    tensorLeftHom_apply, chain_units_smul] at h
  simpa only [one_mul] using h

end SerrePositivity.DifferentialGraded.DGQuotient
