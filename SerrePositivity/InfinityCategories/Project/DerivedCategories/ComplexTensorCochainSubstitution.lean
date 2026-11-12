module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexTensorCochainUnit
/-!
概要：二つの実鎖写像の tensor による前合成を、同じ全 cochain への代入に分解する。
方針：全 Hom tensor の合成保存と、異なる因子に作用する実鎖写像との自然性を使う。
規約：任意の整数次数。使われ方：出力分解の実三重合成の比較成分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable {R : Type u} [CommRing R]
/-- 右 tensor の同じ全 cochain に、二つの実鎖写像を代入する。 -/
lemma complexRightTensorCochain_substitution {P P' Q Q' T : Complex R}
    (f : P ⟶ P') (g : Q ⟶ Q') (p : ℤ) (h : Cochain P' T p) :
    (Cochain.ofHom (f ⊗ₘ g)).comp ((tensorRightHom Q' P' T).f p h) (zero_add p) =
      ((tensorRightHom Q P T).f p ((Cochain.ofHom f).comp h (zero_add p))).comp
        (Cochain.ofHom (T ◁ g)) (add_zero p) := by
  rw [tensorHom_def, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    tensorRight_cochain_chain_naturality,
    ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← tensorRightHom_ofHom, ← tensorRightHom_cochain_comp]
/-- 左 tensor の同じ全 cochain に、二つの実鎖写像を代入する。 -/
lemma complexLeftTensorCochain_substitution {P P' Q Q' T : Complex R}
    (f : P ⟶ P') (g : Q ⟶ Q') (p : ℤ) (h : Cochain Q' T p) :
    (Cochain.ofHom (f ⊗ₘ g)).comp ((tensorLeftHom P' Q' T).f p h) (zero_add p) =
      ((tensorLeftHom P Q T).f p ((Cochain.ofHom g).comp h (zero_add p))).comp
        (Cochain.ofHom (f ▷ T)) (add_zero p) := by
  rw [tensorHom_def', Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexLeftTensor_cochain_chain_naturality,
    ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← tensorLeftHom_ofHom, ← tensorLeftHom_cochain_comp]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
