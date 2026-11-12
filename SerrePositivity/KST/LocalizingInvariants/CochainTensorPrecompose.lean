module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexTensorCochainUnit

/-!
概要：二因子の実鎖写像による前合成と、任意次数 cochain の tensor を比較する。
方針：作用する因子の合成保存と、もう一方の因子の交差自然性を使う。
規約：次数を零に制限しない。使われ方：経路代数の比較 cochain の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {R : Type u} [CommRing R] {K L P Q T : Complex R}

lemma tensorRight_precompose (f : K ⟶ P) (g : L ⟶ Q) (n : ℤ) (h : Cochain P T n) :
    (Cochain.ofHom (f ⊗ₘ g)).comp ((tensorRightHom Q P T).f n h) (zero_add n) =
      ((tensorRightHom L K T).f n ((Cochain.ofHom f).comp h (zero_add n))).comp
        (Cochain.ofHom (T ◁ g)) (add_zero n) := by
  rw [tensorHom_def', Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    ← tensorRightHom_ofHom, ← tensorRightHom_cochain_comp,
    tensorRight_cochain_chain_naturality]

lemma tensorLeft_precompose (f : K ⟶ P) (g : L ⟶ Q) (n : ℤ) (h : Cochain Q T n) :
    (Cochain.ofHom (f ⊗ₘ g)).comp ((tensorLeftHom P Q T).f n h) (zero_add n) =
      ((tensorLeftHom K L T).f n ((Cochain.ofHom g).comp h (zero_add n))).comp
        (Cochain.ofHom (f ▷ T)) (add_zero n) := by
  rw [tensorHom_def, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    ← tensorLeftHom_ofHom, ← tensorLeftHom_cochain_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexLeftTensor_cochain_chain_naturality]

end SerrePositivity.KST.LocalizingInvariants
