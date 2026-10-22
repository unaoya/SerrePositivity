module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathConnectionCochain

/-!
概要：二重経路 connection の比較成分は source 対角と恒等の差を埋める。
方針：全 cochain の一意性と微分の Leibniz 則で三成分を照合する。
規約：乗法性は後続工程。使われ方：実 connection の chain map の持ち上げ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
variable (R : Type u) [CommRing R] (B : Mon (Complex R))

lemma primitive_differential : δ (-1) 0 (primitive R B) =
    Cochain.ofHom ((target R B).hom - (source R B).hom) := by
  have h := primitive_boundary R B
  rw [Cochain.ofHom_sub] at h ⊢
  exact (eq_neg_of_add_eq_zero_left h).trans (by abel)

lemma connectionCochain_differential_primitive :
    (δ (-1) 0 (connectionCochain R B)).comp (primitive R B) (zero_add (-1)) =
      primitive R B := by
  have h := δ_comp (connectionCochain R B) (primitive R B)
    (show -1 + -1 = -2 by omega) 0 0 (-1) (by omega) (by omega) (by omega)
  rw [connectionCochain_primitive, δ_zero, primitive_differential,
    Cochain.ofHom_sub, Cochain.comp_sub, connectionCochain_target,
    connectionCochain_source, sub_zero] at h
  norm_num at h
  exact (sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using h.symm)).symm

lemma connectionCochain_boundary : δ (-1) 0 (connectionCochain R B) +
    Cochain.ofHom ((source R B).hom ≫ diagonalHom R B - 𝟙 (algebra R B).X) = 0 := by
  apply cochain_ext R B
  · rw [Cochain.add_comp, ← δ_comp_ofHom, connectionCochain_source,
      δ_zero, zero_add, ← Cochain.ofHom_comp]
    simp only [Preadditive.sub_comp, Category.assoc, diagonalHom_source,
      Category.comp_id, Category.id_comp, sub_self, Cochain.ofHom_zero,
      Cochain.zero_comp]
  · rw [Cochain.add_comp, ← δ_comp_ofHom, connectionCochain_target,
      primitive_differential, ← Cochain.ofHom_comp]
    simp only [Preadditive.sub_comp, Category.assoc, diagonalHom_target,
      Category.comp_id, Category.id_comp, Cochain.ofHom_sub, Cochain.zero_comp]
    abel
  · rw [Cochain.add_comp, connectionCochain_differential_primitive,
      Cochain.ofHom_sub, Cochain.sub_comp, Cochain.ofHom_comp,
      Cochain.comp_assoc_of_first_is_zero_cochain, diagonalHom_primitive,
      Cochain.comp_zero, Cochain.id_comp, Cochain.zero_comp]
    simp

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
