module

public import SerrePositivity.KST.LocalizingInvariants.CochainTensorPrecompose
public import Mathlib.CategoryTheory.Monoidal.Mon

/-!
概要：全次数の比較 cochain と閉端点の二つの積が、実代数射と可換になる。
方針：tensor の前合成式を使い、閉射の部分を代数射の積保存に戻す。
規約：比較 cochain に閉性は要求しない。使われ方：経路代数の射の積保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CochainComplex HomComplex
open scoped MonObj
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants
variable {R : Type u} [CommRing R] {A B : Mon (Complex R)} (f : A ⟶ B)
  {P Q : Complex R} (k : P ⟶ Q) (a : P ⟶ A.X) (b : Q ⟶ B.X)
  (ha : k ≫ b = a ≫ f.hom) (n : ℤ) (h : Cochain P A.X n) (h' : Cochain Q B.X n)
  (hh : (Cochain.ofHom k).comp h' (zero_add n) = h.comp (Cochain.ofHom f.hom) (add_zero n))

include ha in
lemma rightProduct_natural_closed :
    (f.hom ▷ P) ≫ (B.X ◁ k) ≫ ((𝟙 B.X ⊗ₘ b) ≫ μ[B.X]) =
      ((𝟙 A.X ⊗ₘ a) ≫ μ[A.X]) ≫ f.hom := by
  calc
    _ = (f.hom ⊗ₘ (k ≫ b)) ≫ μ[B.X] := by
      simp only [tensorHom_def, id_whiskerRight, Category.id_comp, whiskerLeft_comp,
        Category.assoc]
    _ = (f.hom ⊗ₘ (a ≫ f.hom)) ≫ μ[B.X] := by rw [ha]
    _ = (𝟙 A.X ⊗ₘ a) ≫ ((f.hom ⊗ₘ f.hom) ≫ μ[B.X]) := by
      rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
    _ = _ := by rw [← IsMonHom.mul_hom, Category.assoc]

include ha hh in
lemma cochainRightProduct_natural :
    (Cochain.ofHom (k ⊗ₘ k)).comp
      (((tensorRightHom Q Q B.X).f n h').comp
        (Cochain.ofHom ((𝟙 B.X ⊗ₘ b) ≫ μ[B.X])) (add_zero n)) (zero_add n) =
      (((tensorRightHom P P A.X).f n h).comp
        (Cochain.ofHom ((𝟙 A.X ⊗ₘ a) ≫ μ[A.X])) (add_zero n)).comp
          (Cochain.ofHom f.hom) (add_zero n) := by
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, tensorRight_precompose, hh,
    tensorRightHom_cochain_comp, tensorRightHom_ofHom,
    Cochain.comp_assoc_of_third_is_zero_cochain,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp,
    ← Cochain.ofHom_comp, rightProduct_natural_closed f k a b ha,
    Cochain.ofHom_comp, ← Cochain.comp_assoc_of_third_is_zero_cochain]

include ha in
lemma leftProduct_natural_closed :
    (P ◁ f.hom) ≫ (k ▷ B.X) ≫ ((b ⊗ₘ 𝟙 B.X) ≫ μ[B.X]) =
      ((a ⊗ₘ 𝟙 A.X) ≫ μ[A.X]) ≫ f.hom := by
  calc
    _ = ((k ≫ b) ⊗ₘ f.hom) ≫ μ[B.X] := by
      simp only [tensorHom_def', whiskerLeft_id, Category.id_comp, comp_whiskerRight,
        Category.assoc]
    _ = ((a ≫ f.hom) ⊗ₘ f.hom) ≫ μ[B.X] := by rw [ha]
    _ = (a ⊗ₘ 𝟙 A.X) ≫ ((f.hom ⊗ₘ f.hom) ≫ μ[B.X]) := by
      rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
    _ = _ := by rw [← IsMonHom.mul_hom, Category.assoc]

include ha hh in
lemma cochainLeftProduct_natural :
    (Cochain.ofHom (k ⊗ₘ k)).comp
      (((tensorLeftHom Q Q B.X).f n h').comp
        (Cochain.ofHom ((b ⊗ₘ 𝟙 B.X) ≫ μ[B.X])) (add_zero n)) (zero_add n) =
      (((tensorLeftHom P P A.X).f n h).comp
        (Cochain.ofHom ((a ⊗ₘ 𝟙 A.X) ≫ μ[A.X])) (add_zero n)).comp
          (Cochain.ofHom f.hom) (add_zero n) := by
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, tensorLeft_precompose, hh,
    tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    Cochain.comp_assoc_of_third_is_zero_cochain,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp,
    ← Cochain.ofHom_comp, leftProduct_natural_closed f k a b ha,
    Cochain.ofHom_comp, ← Cochain.comp_assoc_of_third_is_zero_cochain]

end SerrePositivity.KST.LocalizingInvariants
