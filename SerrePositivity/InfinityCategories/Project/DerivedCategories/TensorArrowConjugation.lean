module
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Basic
/-!
概要：同型による実 tensor 射の共役と Leibniz 式の保存。
方針：tensor の関手性と同型の両逆性、加法・整数倍の自然性を使う。
規約：微分や乗法のデータを変更しない。使われ方：β5(g) の係数・次数移送。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
def tensorArrowConjugate {P Q T P' Q' T' : C}
    (a : P ≅ P') (b : Q ≅ Q') (c : T ≅ T') (m : P' ⊗ Q' ⟶ T') : P ⊗ Q ⟶ T :=
  (a.hom ⊗ₘ b.hom) ≫ m ≫ c.inv
lemma tensorArrowConjugate_post {P Q T P' Q' T' : C}
    (a : P ≅ P') (b : Q ≅ Q') (c : T ≅ T') (m : P' ⊗ Q' ⟶ T') :
    tensorArrowConjugate a b c m ≫ c.hom = (a.hom ⊗ₘ b.hom) ≫ m := by
  simp only [tensorArrowConjugate, Category.assoc, Iso.inv_hom_id, Category.comp_id]
lemma tensorArrowConjugate_left {P₀ P₁ Q T P₀' P₁' Q' T' : C}
    (a₀ : P₀ ≅ P₀') (a₁ : P₁ ≅ P₁') (b : Q ≅ Q') (c : T ≅ T')
    (f : P₀' ⟶ P₁') (m : P₁' ⊗ Q' ⟶ T') :
    ((a₀.hom ≫ f ≫ a₁.inv) ⊗ₘ 𝟙 Q) ≫ tensorArrowConjugate a₁ b c m =
      tensorArrowConjugate a₀ b c ((f ⊗ₘ 𝟙 Q') ≫ m) := by
  dsimp only [tensorArrowConjugate]
  simp only [← Category.assoc, tensorHom_comp_tensorHom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
lemma tensorArrowConjugate_right {P Q₀ Q₁ T P' Q₀' Q₁' T' : C}
    (a : P ≅ P') (b₀ : Q₀ ≅ Q₀') (b₁ : Q₁ ≅ Q₁') (c : T ≅ T')
    (g : Q₀' ⟶ Q₁') (m : P' ⊗ Q₁' ⟶ T') :
    (𝟙 P ⊗ₘ (b₀.hom ≫ g ≫ b₁.inv)) ≫ tensorArrowConjugate a b₁ c m =
      tensorArrowConjugate a b₀ c ((𝟙 P' ⊗ₘ g) ≫ m) := by
  dsimp only [tensorArrowConjugate]
  simp only [← Category.assoc, tensorHom_comp_tensorHom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
lemma tensorArrowConjugate_post_conjugate {P Q T₀ T₁ P' Q' T₀' T₁' : C}
    (a : P ≅ P') (b : Q ≅ Q') (c₀ : T₀ ≅ T₀') (c₁ : T₁ ≅ T₁')
    (m : P' ⊗ Q' ⟶ T₀') (d : T₀' ⟶ T₁') :
    tensorArrowConjugate a b c₀ m ≫ (c₀.hom ≫ d ≫ c₁.inv) =
      tensorArrowConjugate a b c₁ (m ≫ d) := by
  simp only [tensorArrowConjugate, Category.assoc, Iso.inv_hom_id_assoc]
lemma tensorArrowConjugate_leibniz_left
    {P₀ P₁ Q T₀ T₁ P₀' P₁' Q' T₀' T₁' : C}
    (a₀ : P₀ ≅ P₀') (a₁ : P₁ ≅ P₁') (b : Q ≅ Q')
    (c₀ : T₀ ≅ T₀') (c₁ : T₁ ≅ T₁')
    (dP : P₀' ⟶ P₁') (dT : T₀' ⟶ T₁')
    (m : P₀' ⊗ Q' ⟶ T₀') (mL : P₁' ⊗ Q' ⟶ T₁')
    (h : m ≫ dT = (dP ⊗ₘ 𝟙 Q') ≫ mL) :
    tensorArrowConjugate a₀ b c₀ m ≫ (c₀.hom ≫ dT ≫ c₁.inv) =
      ((a₀.hom ≫ dP ≫ a₁.inv) ⊗ₘ 𝟙 Q) ≫ tensorArrowConjugate a₁ b c₁ mL := by
  rw [tensorArrowConjugate_post_conjugate, h, ← tensorArrowConjugate_left]
lemma tensorArrowConjugate_leibniz_right
    {P Q₀ Q₁ T₀ T₁ P' Q₀' Q₁' T₀' T₁' : C}
    (a : P ≅ P') (b₀ : Q₀ ≅ Q₀') (b₁ : Q₁ ≅ Q₁')
    (c₀ : T₀ ≅ T₀') (c₁ : T₁ ≅ T₁')
    (dQ : Q₀' ⟶ Q₁') (dT : T₀' ⟶ T₁')
    (m : P' ⊗ Q₀' ⟶ T₀') (mR : P' ⊗ Q₁' ⟶ T₁')
    (h : m ≫ dT = (𝟙 P' ⊗ₘ dQ) ≫ mR) :
    tensorArrowConjugate a b₀ c₀ m ≫ (c₀.hom ≫ dT ≫ c₁.inv) =
      (𝟙 P ⊗ₘ (b₀.hom ≫ dQ ≫ b₁.inv)) ≫ tensorArrowConjugate a b₁ c₁ mR := by
  rw [tensorArrowConjugate_post_conjugate, h, ← tensorArrowConjugate_right]
variable [Preadditive C]
lemma tensorArrowConjugate_add {P Q T P' Q' T' : C}
    (a : P ≅ P') (b : Q ≅ Q') (c : T ≅ T') (m n : P' ⊗ Q' ⟶ T') :
    tensorArrowConjugate a b c (m + n) =
      tensorArrowConjugate a b c m + tensorArrowConjugate a b c n := by
  simp only [tensorArrowConjugate, Preadditive.add_comp, Preadditive.comp_add]
lemma tensorArrowConjugate_zsmul {P Q T P' Q' T' : C}
    (a : P ≅ P') (b : Q ≅ Q') (c : T ≅ T') (s : ℤ) (m : P' ⊗ Q' ⟶ T') :
    tensorArrowConjugate a b c (s • m) = s • tensorArrowConjugate a b c m := by
  simp only [tensorArrowConjugate, Preadditive.zsmul_comp, Preadditive.comp_zsmul]
lemma tensorArrowConjugate_leibniz
    {P₀ P₁ Q₀ Q₁ T₀ T₁ P₀' P₁' Q₀' Q₁' T₀' T₁' : C}
    (a₀ : P₀ ≅ P₀') (a₁ : P₁ ≅ P₁') (b₀ : Q₀ ≅ Q₀') (b₁ : Q₁ ≅ Q₁')
    (c₀ : T₀ ≅ T₀') (c₁ : T₁ ≅ T₁')
    (dP : P₀' ⟶ P₁') (dQ : Q₀' ⟶ Q₁') (dT : T₀' ⟶ T₁')
    (m : P₀' ⊗ Q₀' ⟶ T₀') (mL : P₁' ⊗ Q₀' ⟶ T₁') (mR : P₀' ⊗ Q₁' ⟶ T₁')
    (s : ℤ) (h : m ≫ dT = (dP ⊗ₘ 𝟙 Q₀') ≫ mL + s • ((𝟙 P₀' ⊗ₘ dQ) ≫ mR)) :
    tensorArrowConjugate a₀ b₀ c₀ m ≫ (c₀.hom ≫ dT ≫ c₁.inv) =
    ((a₀.hom ≫ dP ≫ a₁.inv) ⊗ₘ 𝟙 Q₀) ≫ tensorArrowConjugate a₁ b₀ c₁ mL +
    s • ((𝟙 P₀ ⊗ₘ (b₀.hom ≫ dQ ≫ b₁.inv)) ≫ tensorArrowConjugate a₀ b₁ c₁ mR) := by
  rw [tensorArrowConjugate_post_conjugate, h, tensorArrowConjugate_add,
    tensorArrowConjugate_zsmul, ← tensorArrowConjugate_left, ← tensorArrowConjugate_right]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
