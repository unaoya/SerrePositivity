module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathConnectionHom
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathProductPrimitive

/-!
概要：connection の内側両評価と単位保存を、元の全 cochain で検証する。
方針：両端・比較成分の一意性を二重に使う。
規約：乗法保存は別工程。使われ方：動く四辺の輪郭比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CochainComplex HomComplex
open scoped MonObj
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
variable (R : Type u) [CommRing R] (B : Mon (Complex R))

lemma connectionCochain_one : (Cochain.ofHom η[(algebra R B).X]).comp
    (connectionCochain R B) (zero_add (-1)) = 0 := by
  apply cochain_ext R B
  · rw [Cochain.comp_assoc_of_first_is_zero_cochain, connectionCochain_source,
      Cochain.comp_zero, Cochain.zero_comp]
  · rw [Cochain.comp_assoc_of_first_is_zero_cochain, connectionCochain_target,
      one_primitive, Cochain.zero_comp]
  · rw [Cochain.comp_assoc_of_first_is_zero_cochain, connectionCochain_primitive,
      Cochain.comp_zero, Cochain.zero_comp]

lemma connectionHom_one : η[(algebra R B).X] ≫ connectionHom R B =
    η[(algebra R (algebra R B)).X] := by
  apply chain_ext R (algebra R B)
  · rw [Category.assoc, connectionHom_source, ← Category.assoc,
      IsMonHom.one_hom, diagonalHom_one]
    exact (IsMonHom.one_hom (source R (algebra R B)).hom).symm
  · rw [Category.assoc, connectionHom_target, Category.comp_id]
    exact (IsMonHom.one_hom (target R (algebra R B)).hom).symm
  · rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
      connectionHom_primitive, connectionCochain_one, one_primitive]

lemma connectionHom_innerSource : connectionHom R B ≫ mapHom R (source R B) =
    (source R B).hom ≫ diagonalHom R B := by
  apply chain_ext R B
  · rw [Category.assoc, mapHom_source, ← Category.assoc, connectionHom_source,
      Category.assoc, diagonalHom_source, Category.comp_id]
  · rw [Category.assoc, mapHom_target, ← Category.assoc, connectionHom_target,
      Category.id_comp, Category.assoc, diagonalHom_target, Category.comp_id]
  · rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
      mapHom_primitive, ← Cochain.comp_assoc_of_first_is_zero_cochain,
      connectionHom_primitive, connectionCochain_source, Cochain.ofHom_comp,
      Cochain.comp_assoc_of_first_is_zero_cochain, diagonalHom_primitive, Cochain.comp_zero]

lemma connectionHom_innerTarget : connectionHom R B ≫ mapHom R (target R B) =
    𝟙 (algebra R B).X := by
  apply chain_ext R B
  · rw [Category.assoc, mapHom_source, ← Category.assoc, connectionHom_source,
      Category.assoc, diagonalHom_target, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, mapHom_target, ← Category.assoc, connectionHom_target,
      Category.id_comp]
  · rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
      mapHom_primitive, ← Cochain.comp_assoc_of_first_is_zero_cochain,
      connectionHom_primitive, connectionCochain_target, Cochain.id_comp]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
