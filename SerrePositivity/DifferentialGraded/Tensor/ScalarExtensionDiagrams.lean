module
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtension

/-! # tensor 式の係数変更を組み立てる比較射 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

def compareTensor {P Q : Complex A} {P' Q' : Complex A'}
    (a : (extension φ).obj P ⟶ P') (b : (extension φ).obj Q ⟶ Q') :
    (extension φ).obj (P ⊗ Q) ⟶ P' ⊗ Q' :=
  (tensorIso φ P Q).hom ≫ (a ⊗ₘ b)

lemma compareTensor_naturality {P Q R T : Complex A} {P' Q' R' T' : Complex A'}
    {a : (extension φ).obj P ⟶ P'} {b : (extension φ).obj Q ⟶ Q'}
    {c : (extension φ).obj R ⟶ R'} {d : (extension φ).obj T ⟶ T'}
    (f : P ⟶ R) (g : Q ⟶ T) (f' : P' ⟶ R') (g' : Q' ⟶ T')
    (hf : (extension φ).map f ≫ c = a ≫ f')
    (hg : (extension φ).map g ≫ d = b ≫ g') :
    (extension φ).map (f ⊗ₘ g) ≫ compareTensor φ c d =
      compareTensor φ a b ≫ (f' ⊗ₘ g') := by
  unfold compareTensor
  rw [← Category.assoc, tensorIso_naturality, Category.assoc,
    tensorHom_comp_tensorHom, hf, hg, ← tensorHom_comp_tensorHom, Category.assoc]

lemma compareTensor_associator {P Q R : Complex A} {P' Q' R' : Complex A'}
    (a : (extension φ).obj P ⟶ P') (b : (extension φ).obj Q ⟶ Q')
    (c : (extension φ).obj R ⟶ R') :
    (extension φ).map (α_ P Q R).hom ≫ compareTensor φ a (compareTensor φ b c) =
      compareTensor φ (compareTensor φ a b) c ≫ (α_ P' Q' R').hom := by
  have hl : a ⊗ₘ ((tensorIso φ Q R).hom ≫ (b ⊗ₘ c)) =
      ((extension φ).obj P ◁ (tensorIso φ Q R).hom) ≫ (a ⊗ₘ (b ⊗ₘ c)) := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp]
  have hr : ((tensorIso φ P Q).hom ≫ (a ⊗ₘ b)) ⊗ₘ c =
      ((tensorIso φ P Q).hom ▷ (extension φ).obj R) ≫ ((a ⊗ₘ b) ⊗ₘ c) := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp]
  unfold compareTensor
  rw [hl, hr]
  simp only [Category.assoc]
  rw [← tensorIso_associator_assoc]
  rw [← associator_naturality]

lemma compareTensor_associator_inv {P Q R : Complex A} {P' Q' R' : Complex A'}
    (a : (extension φ).obj P ⟶ P') (b : (extension φ).obj Q ⟶ Q')
    (c : (extension φ).obj R ⟶ R') :
    (extension φ).map (α_ P Q R).inv ≫ compareTensor φ (compareTensor φ a b) c =
      compareTensor φ a (compareTensor φ b c) ≫ (α_ P' Q' R').inv := by
  have h := congrArg (fun f => (extension φ).map (α_ P Q R).inv ≫ f ≫ (α_ P' Q' R').inv)
    (compareTensor_associator φ a b c)
  simp only [← Category.assoc, ← CategoryTheory.Functor.map_comp,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp] at h
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h.symm

lemma compareTensor_leftUnitor {P : Complex A} {P' : Complex A'}
    (a : (extension φ).obj P ⟶ P') :
    (extension φ).map (λ_ P).hom ≫ a =
      compareTensor φ (unitIso φ).hom a ≫ (λ_ P').hom := by
  have h := Functor.Monoidal.map_leftUnitor (extension φ) P
  change (extension φ).map (λ_ P).hom =
    (tensorIso φ (𝟙_ (Complex A)) P).hom ≫
      (unitIso φ).hom ▷ (extension φ).obj P ≫ (λ_ ((extension φ).obj P)).hom at h
  rw [h]
  unfold compareTensor
  rw [← tensorHom_id, Category.assoc, Category.assoc, ← leftUnitor_naturality,
    ← id_tensorHom, tensorHom_comp_tensorHom_assoc]
  simp only [Category.comp_id, Category.id_comp, Category.assoc]

end SerrePositivity.DifferentialGraded.ScalarExtension
