module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathProductPrimitive

/-!
概要：比較成分が零の cochain の積の、同じ経路 primitive による零化。
方針：経路乗法の二比較項を tensor の合成則と自然性で消去する。
規約：閉性を仮定しない。使われ方：connection の乗法保存の二重 primitive。
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

lemma rightProduct_primitive_zero {P Q : Complex R}
    (h : Cochain P (algebra R B).X (-1)) (a : Q ⟶ (algebra R B).X)
    (hh : h.comp (primitive R B) (show -1 + -1 = -2 by omega) = 0)
    (ha : (Cochain.ofHom a).comp (primitive R B) (zero_add (-1)) = 0) :
    (((tensorRightHom Q P (algebra R B).X).f (-1) h).comp
      (Cochain.ofHom ((𝟙 (algebra R B).X ⊗ₘ a) ≫ μ[(algebra R B).X]))
      (add_zero (-1))).comp (primitive R B) (show -1 + -1 = -2 by omega) = 0 := by
  rw [Cochain.comp_assoc_of_second_is_zero_cochain, Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain, mul_primitive, Cochain.comp_add,
    ← Cochain.comp_assoc_of_first_is_zero_cochain,
    tensorRight_precompose, Cochain.id_comp,
    ← Cochain.comp_assoc_of_first_is_zero_cochain,
    tensorLeft_precompose, ha, map_zero, Cochain.zero_comp, Cochain.zero_comp,
    add_zero]
  rw [Cochain.comp_assoc_of_second_is_zero_cochain,
    ← Cochain.comp_assoc_of_third_is_zero_cochain,
    ← Cochain.comp_assoc_of_third_is_zero_cochain,
    ← tensorRightHom_cochain_comp, hh, map_zero, Cochain.zero_comp, Cochain.zero_comp]

lemma leftProduct_primitive_zero {P Q : Complex R}
    (a : P ⟶ (algebra R B).X) (h : Cochain Q (algebra R B).X (-1))
    (hs : h.comp (Cochain.ofHom (source R B).hom) (add_zero (-1)) = 0)
    (hh : h.comp (primitive R B) (show -1 + -1 = -2 by omega) = 0) :
    (((tensorLeftHom P Q (algebra R B).X).f (-1) h).comp
      (Cochain.ofHom ((a ⊗ₘ 𝟙 (algebra R B).X) ≫ μ[(algebra R B).X]))
      (add_zero (-1))).comp (primitive R B) (show -1 + -1 = -2 by omega) = 0 := by
  rw [Cochain.comp_assoc_of_second_is_zero_cochain, Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain, mul_primitive, Cochain.comp_add,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, tensorRight_precompose,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, tensorLeft_precompose,
    Cochain.id_comp, Cochain.comp_add]
  have h₁ : Cochain.comp ((tensorLeftHom P Q (algebra R B).X).f (-1) h)
      (((tensorRightHom (algebra R B).X P B.X).f (-1)
        ((Cochain.ofHom a).comp (primitive R B) (zero_add (-1)))).comp
          (Cochain.ofHom ((𝟙 B.X ⊗ₘ (source R B).hom) ≫ μ[B.X]))
          (add_zero (-1))) (show -1 + -1 = -2 by omega) = 0 := by
    rw [Cochain.ofHom_comp, ← Cochain.comp_assoc_of_third_is_zero_cochain,
      tensorHom_def, id_whiskerRight, Category.id_comp,
      ← Cochain.comp_assoc_of_third_is_zero_cochain,
      Cochain.comp_assoc_of_third_is_zero_cochain
        ((tensorLeftHom P Q (algebra R B).X).f (-1) h)
        ((tensorRightHom (algebra R B).X P B.X).f (-1)
          ((Cochain.ofHom a).comp (primitive R B) (zero_add (-1))))
        (Cochain.ofHom (B.X ◁ (source R B).hom)) (show -1 + -1 = -2 by omega),
      ← tensorRight_cochain_chain_naturality,
      ← Cochain.comp_assoc_of_second_is_zero_cochain,
      ← tensorLeftHom_ofHom, ← tensorLeftHom_cochain_comp, hs, map_zero,
      Cochain.zero_comp, Cochain.zero_comp]
  have h₂ : Cochain.comp ((tensorLeftHom P Q (algebra R B).X).f (-1) h)
      ((((tensorLeftHom P (algebra R B).X B.X).f (-1) (primitive R B)).comp
        (Cochain.ofHom (a ▷ B.X)) (add_zero (-1))).comp
          (Cochain.ofHom (((target R B).hom ⊗ₘ 𝟙 B.X) ≫ μ[B.X]))
          (add_zero (-1))) (show -1 + -1 = -2 by omega) = 0 := by
    rw [← Cochain.comp_assoc_of_third_is_zero_cochain,
      ← Cochain.comp_assoc_of_third_is_zero_cochain,
      ← tensorLeftHom_cochain_comp, hh, map_zero, Cochain.zero_comp, Cochain.zero_comp]
  rw [whiskerLeft_id, Cochain.comp_id, h₁, h₂, zero_add]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
