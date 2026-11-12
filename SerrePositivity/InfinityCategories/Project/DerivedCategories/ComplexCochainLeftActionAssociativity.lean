module
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoin
/-!
概要：三重 tensor の右端の全 cochain と、前二因子の実合成の括弧変更を比較する。
方針：結合子の全 cochain 自然性と、実 tensor の合成保存を使う。
規約：任意の整数次数。使われ方：出力分解の結合律の第三比較項。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable {R : Type u} [CommRing R]
/-- 右端の同じ全 cochain への、結合的な実左作用の三重合成。 -/
lemma complexCochain_tensorLeft_action_assoc (P Q H T T' U V : Complex R) (p : ℤ)
    (f : Cochain T T' p) (m : P ⊗ Q ⟶ H) (n : Q ⊗ T' ⟶ U)
    (r : P ⊗ U ⟶ V) (s : H ⊗ T' ⟶ V)
    (ha : (m ▷ T') ≫ s = (α_ P Q T').hom ≫ P ◁ n ≫ r) :
    (Cochain.ofHom (m ▷ T)).comp
      (((tensorLeftHom H T T').f p f).comp (Cochain.ofHom s) (add_zero p))
      (zero_add p) =
    (Cochain.ofHom (α_ P Q T).hom).comp
      (((tensorLeftHom P (Q ⊗ T) U).f p
        (((tensorLeftHom Q T T').f p f).comp (Cochain.ofHom n) (add_zero p))).comp
        (Cochain.ofHom r) (add_zero p)) (zero_add p) := by
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← tensorLeftHom_cochain_naturality,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, ha,
    Cochain.ofHom_comp, ← Cochain.comp_assoc_of_third_is_zero_cochain,
    associator_hom_cochain_right]
  simp only [tensorLeftHom_cochain_comp, tensorLeftHom_ofHom, Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain,
    Cochain.comp_assoc_of_third_is_zero_cochain]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
