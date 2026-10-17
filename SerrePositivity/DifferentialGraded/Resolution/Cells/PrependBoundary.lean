module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.PrependBoundaryRows
public import SerrePositivity.DifferentialGraded.Resolution.Cells.TensorPathCochainExt

/-! # 任意次数cell path：PrependBoundary -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits Preadditive MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

/-- 空pathを左に置く合成の境界置換Leibniz則。左の元のHomには消去項がない。 -/
lemma internalPrepend_replacement (x y z : D) :
    (Cochain.ofHom (C.internalPrepend A D I x y z)).comp (C.replacement A D I x z) (zero_add 1) =
    ((tensorLeftHom (homObject A D x y) (C.internalHom A D I y z)
      (C.internalHom A D I y z)).f 1 (C.replacement A D I y z)).comp
      (Cochain.ofHom (C.internalPrepend A D I x y z)) (add_zero 1) := by
  apply C.tensorLeftPathCochain_ext A D I y z (homObject A D x y) 1
  intro w
  have hb : (Cochain.ofHom ((homObject A D x y) ◁ C.inclusion A D I w y z)).comp
      ((tensorLeftHom (homObject A D x y) (C.internalHom A D I y z)
        (C.internalHom A D I y z)).f 1 (C.replacement A D I y z)) (zero_add 1) =
      (tensorLeftHom (homObject A D x y) (C.term A D I w y z)
        (C.internalHom A D I y z)).f 1 (C.replaceRow A D I w y z) := by
    rw [← tensorLeftHom_ofHom, ← tensorLeftHom_cochain_comp, replacement_precomp]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    internalPrepend_inclusion, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    replacement_precomp, ← Cochain.comp_assoc_of_first_is_zero_cochain, hb]
  exact C.prependMap_replaceRow A D I w x y z

/-- 空pathを左に置く消去Leibniz則の斉次成分。右側の消去には(-1)^pが付く。 -/
lemma internalPrepend_replacement_apply (x y z : D) (p q n : ℤ)
    (hn : p + q = n) (a : (homObject A D x y).X p) (b : (C.internalHom A D I y z).X q) :
    (C.replacement A D I x z).v n (n + 1) rfl
      ((C.internalPrepend A D I x y z).f n
        (ιTensorObj (homObject A D x y) (C.internalHom A D I y z) p q n hn (a ⊗ₜ[A] b))) =
    p.negOnePow • (C.internalPrepend A D I x y z).f (n + 1)
      (ιTensorObj (homObject A D x y) (C.internalHom A D I y z) p (q + 1) (n + 1)
        (by omega) (a ⊗ₜ[A] (C.replacement A D I y z).v q (q + 1) rfl b)) := by
  have h := congrArg (fun f : Cochain
      (homObject A D x y ⊗ C.internalHom A D I y z) (C.internalHom A D I x z) 1 =>
    f.v n (n + 1) rfl
      (ιTensorObj (homObject A D x y) (C.internalHom A D I y z) p q n hn (a ⊗ₜ[A] b)))
    (C.internalPrepend_replacement A D I x y z)
  rw [cochain_ofHom_comp_apply, cochain_comp_ofHom_apply,
    tensorLeftHom_apply, chain_units_smul] at h
  simpa only [one_mul] using h

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
