module

public import SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochain



/-!
概要：鎖写像の前合成で零となる全次数 cochain は、二因子の tensor でも零となる。
方針：同じ因子の合成を tensor してから、もう一つの因子を前合成する。
規約：閉 cochain とは仮定しない。使われ方：経路代数の対角の積保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants
variable {R : Type u} [CommRing R] {K L P Q T : Complex R}

lemma tensorRight_precompose_zero (f : K ⟶ P) (g : L ⟶ Q) (n : ℤ)
    (h : Cochain P T n) (hf : (Cochain.ofHom f).comp h (zero_add n) = 0) :
    (Cochain.ofHom (f ⊗ₘ g)).comp ((tensorRightHom Q P T).f n h) (zero_add n) = 0 := by
  rw [tensorHom_def', Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    ← tensorRightHom_ofHom, ← tensorRightHom_cochain_comp, hf, map_zero, Cochain.comp_zero]

lemma tensorLeft_precompose_zero (f : K ⟶ P) (g : L ⟶ Q) (n : ℤ)
    (h : Cochain Q T n) (hg : (Cochain.ofHom g).comp h (zero_add n) = 0) :
    (Cochain.ofHom (f ⊗ₘ g)).comp ((tensorLeftHom P Q T).f n h) (zero_add n) = 0 := by
  rw [tensorHom_def, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    ← tensorLeftHom_ofHom, ← tensorLeftHom_cochain_comp, hg, map_zero, Cochain.comp_zero]

end SerrePositivity.KST.LocalizingInvariants
