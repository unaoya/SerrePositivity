module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexTensorCochainUnit
/-!
概要：全次数 cochain の可換四角形を左右 tensor と後合成へ移す。
方針：全 Hom tensor の合成保存と、閉零鎖写像との符号付き自然性を使う。
規約：任意の整数次数・全非有界複体。使われ方：分解変更の合成比較 cochain。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable {R : Type u} [CommRing R]
/-- 同じ全 cochain 四角形は、第二因子も同時に移す右 tensor と整合する。 -/
lemma tensorRight_cochain_square {P P' H H' Q Q' : Complex R} (n : ℤ)
    (f : P ⟶ P') (g : Q ⟶ Q') (k : H ⟶ H')
    (h : Cochain P H n) (h' : Cochain P' H' n)
    (hh : (Cochain.ofHom f).comp h' (zero_add n) =
      h.comp (Cochain.ofHom k) (add_zero n)) :
    (Cochain.ofHom (f ⊗ₘ g)).comp ((tensorRightHom Q' P' H').f n h') (zero_add n) =
      ((tensorRightHom Q P H).f n h).comp (Cochain.ofHom (k ⊗ₘ g)) (add_zero n) := by
  rw [tensorHom_def, Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain, tensorRight_cochain_chain_naturality,
    ← Cochain.comp_assoc_of_third_is_zero_cochain, ← tensorRightHom_ofHom,
    ← tensorRightHom_cochain_comp, hh, tensorRightHom_cochain_comp, tensorRightHom_ofHom,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, ← tensorHom_def]
/-- 同じ全 cochain 四角形は、第一因子も同時に移す左 tensor と整合する。 -/
lemma tensorLeft_cochain_square {P P' H H' Q Q' : Complex R} (n : ℤ)
    (f : P ⟶ P') (g : Q ⟶ Q') (k : H ⟶ H')
    (h : Cochain Q H n) (h' : Cochain Q' H' n)
    (hh : (Cochain.ofHom g).comp h' (zero_add n) =
      h.comp (Cochain.ofHom k) (add_zero n)) :
    (Cochain.ofHom (f ⊗ₘ g)).comp ((tensorLeftHom P' Q' H').f n h') (zero_add n) =
      ((tensorLeftHom P Q H).f n h).comp (Cochain.ofHom (f ⊗ₘ k)) (add_zero n) := by
  rw [tensorHom_def', Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexLeftTensor_cochain_chain_naturality,
    ← Cochain.comp_assoc_of_third_is_zero_cochain, ← tensorLeftHom_ofHom,
    ← tensorLeftHom_cochain_comp, hh, tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, ← tensorHom_def']
/-- 全 cochain 四角形に沿う後合成は、同じ実鎖写像の四角形を保つ。 -/
lemma cochain_postcompose_square {P P' H H' T T' : Complex R} (n : ℤ)
    (f : P ⟶ P') (g : H ⟶ H') (r : T ⟶ T')
    (k : H ⟶ T) (k' : H' ⟶ T') (h : Cochain P H n) (h' : Cochain P' H' n)
    (hh : (Cochain.ofHom f).comp h' (zero_add n) =
      h.comp (Cochain.ofHom g) (add_zero n))
    (hk : g ≫ k' = k ≫ r) :
    (Cochain.ofHom f).comp (h'.comp (Cochain.ofHom k') (add_zero n)) (zero_add n) =
      (h.comp (Cochain.ofHom k) (add_zero n)).comp (Cochain.ofHom r) (add_zero n) := by
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, hh,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, hk,
    Cochain.ofHom_comp, ← Cochain.comp_assoc_of_third_is_zero_cochain]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
