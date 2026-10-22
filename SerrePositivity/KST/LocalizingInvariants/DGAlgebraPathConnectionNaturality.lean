module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathConnectionAlgebra

/-!
概要：経路 connection の自然性と、定数経路上での二重対角との一致。
方針：両評価と比較 cochain を、経路内でも同じ三成分で比較する。
規約：等式は全実代数射で成立。使われ方：相対 class 二重経路の底射影の保持。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
variable (R : Type u) [CommRing R]

lemma connectionCochain_naturality {A B : Mon (Complex R)} (f : A ⟶ B) :
    (Cochain.ofHom (mapHom R f)).comp (connectionCochain R B) (zero_add (-1)) =
      (connectionCochain R A).comp (Cochain.ofHom (mapHom R f)) (add_zero (-1)) := by
  apply cochain_ext R B
  · rw [Cochain.comp_assoc_of_first_is_zero_cochain, connectionCochain_source,
      Cochain.comp_zero, Cochain.comp_assoc_of_third_is_zero_cochain,
      ← Cochain.ofHom_comp, mapHom_source, Cochain.ofHom_comp,
      ← Cochain.comp_assoc_of_third_is_zero_cochain, connectionCochain_source,
      Cochain.zero_comp]
  · rw [Cochain.comp_assoc_of_first_is_zero_cochain, connectionCochain_target,
      mapHom_primitive, Cochain.comp_assoc_of_third_is_zero_cochain,
      ← Cochain.ofHom_comp, mapHom_target, Cochain.ofHom_comp,
      ← Cochain.comp_assoc_of_third_is_zero_cochain, connectionCochain_target]
  · rw [Cochain.comp_assoc_of_first_is_zero_cochain, connectionCochain_primitive,
      Cochain.comp_zero, Cochain.comp_assoc_of_second_is_zero_cochain,
      mapHom_primitive, ← Cochain.comp_assoc_of_third_is_zero_cochain,
      connectionCochain_primitive, Cochain.zero_comp]

lemma connection_naturality {A B : Mon (Complex R)} (f : A ⟶ B) :
    map R f ≫ connection R B = connection R A ≫ map R (map R f) := by
  apply Mon.Hom.ext
  apply chain_ext R (algebra R B)
  · change (mapHom R f ≫ connectionHom R B) ≫ (source R (algebra R B)).hom =
      (connectionHom R A ≫ mapHom R (map R f)) ≫ (source R (algebra R B)).hom
    rw [Category.assoc, connectionHom_source, Category.assoc, mapHom_source]
    rw [← Category.assoc (mapHom R f), mapHom_source,
      ← Category.assoc (connectionHom R A), connectionHom_source]
    simp only [Category.assoc]
    exact congrArg (fun k => (source R A).hom ≫ k)
      (congrArg Mon.Hom.hom (diagonal_naturality R f)).symm
  · change (mapHom R f ≫ connectionHom R B) ≫ (target R (algebra R B)).hom =
      (connectionHom R A ≫ mapHom R (map R f)) ≫ (target R (algebra R B)).hom
    rw [Category.assoc, connectionHom_target, Category.comp_id, Category.assoc,
      mapHom_target, ← Category.assoc, connectionHom_target, Category.id_comp]
    rfl
  · change (Cochain.ofHom (mapHom R f ≫ connectionHom R B)).comp _ _ =
      (Cochain.ofHom (connectionHom R A ≫ mapHom R (map R f))).comp _ _
    rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
      connectionHom_primitive, Cochain.ofHom_comp,
      Cochain.comp_assoc_of_first_is_zero_cochain, mapHom_primitive,
      ← Cochain.comp_assoc_of_first_is_zero_cochain, connectionHom_primitive]
    exact connectionCochain_naturality R f

lemma connectionCochain_diagonal (B : Mon (Complex R)) :
    (Cochain.ofHom (diagonalHom R B)).comp (connectionCochain R B) (zero_add (-1)) = 0 := by
  apply cochain_ext R B
  · rw [Cochain.comp_assoc_of_first_is_zero_cochain, connectionCochain_source,
      Cochain.comp_zero, Cochain.zero_comp]
  · rw [Cochain.comp_assoc_of_first_is_zero_cochain, connectionCochain_target,
      diagonalHom_primitive, Cochain.zero_comp]
  · rw [Cochain.comp_assoc_of_first_is_zero_cochain, connectionCochain_primitive,
      Cochain.comp_zero, Cochain.zero_comp]

lemma diagonal_connection (B : Mon (Complex R)) : diagonal R B ≫ connection R B =
    diagonal R B ≫ diagonal R (algebra R B) := by
  apply Mon.Hom.ext
  apply chain_ext R (algebra R B)
  · change (diagonalHom R B ≫ connectionHom R B) ≫ (source R (algebra R B)).hom =
      (diagonalHom R B ≫ diagonalHom R (algebra R B)) ≫ _
    rw [Category.assoc, connectionHom_source, ← Category.assoc, diagonalHom_source,
      Category.id_comp, Category.assoc, diagonalHom_source, Category.comp_id]
  · change (diagonalHom R B ≫ connectionHom R B) ≫ (target R (algebra R B)).hom =
      (diagonalHom R B ≫ diagonalHom R (algebra R B)) ≫ _
    rw [Category.assoc, connectionHom_target, Category.comp_id, Category.assoc,
      diagonalHom_target, Category.comp_id]
  · change (Cochain.ofHom (diagonalHom R B ≫ connectionHom R B)).comp _ _ =
      (Cochain.ofHom (diagonalHom R B ≫ diagonalHom R (algebra R B))).comp _ _
    rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
      connectionHom_primitive, connectionCochain_diagonal, Cochain.ofHom_comp,
      Cochain.comp_assoc_of_first_is_zero_cochain, diagonalHom_primitive, Cochain.comp_zero]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
