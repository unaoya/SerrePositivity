module

public import SerrePositivity.CategoryTheory.Monoidal.RepresentedMappingEnrichment

/-! # Evaluation of composition with an ordinary arrow

One ordinary arrow and one arbitrary mapping-object parameter suffice to recover
mapping functoriality. These laws do not assume that unit-valued points detect
all morphisms of the enriching category.
-/

@[expose] public section
universe v₁ v₂ u₁ u₂
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace SerrePositivity.MappingWhiskering
variable {V : Type u₁} {D : Type u₂} [Category.{v₁} V] [Category.{v₂} D]
  [MonoidalCategory V] (H : V ⥤ D ⥤ D)
  (a : ∀ P Q : V, H.obj (P ⊗ Q) ≅ H.obj Q ⋙ H.obj P)
  (u : H.obj (𝟙_ V) ≅ 𝟭 D)

/-- Evaluate a composition whose final arrow is an ordinary arrow. -/
lemma post_evaluation {P Q : V} {E F G : D} (p : 𝟙_ V ⟶ P) (g : F ⟶ G)
    (v : (H.obj Q).obj E ⟶ F) (w : (H.obj P).obj F ⟶ G)
    (hp : (H.map p).app F ≫ w = u.hom.app F ≫ g)
    (hn : (H.map (p ⊗ₘ 𝟙 Q)).app E ≫ (a P Q).hom.app E =
      (a (𝟙_ V) Q).hom.app E ≫ (H.map p).app ((H.obj Q).obj E))
    (hu : (a (𝟙_ V) Q).hom.app E ≫ u.hom.app ((H.obj Q).obj E) =
      (H.map (λ_ Q).hom).app E) :
    (H.map (p ⊗ₘ 𝟙 Q)).app E ≫
        MappingAssociativity.compositionEvaluation H a P Q v w =
      (H.map (λ_ Q).hom).app E ≫ v ≫ g := by
  unfold MappingAssociativity.compositionEvaluation
  rw [reassoc_of% hn, ← reassoc_of% ((H.map p).naturality v), hp]
  rw [reassoc_of% (u.hom.naturality v), reassoc_of% hu]

/-- Evaluate a composition whose initial arrow is an ordinary arrow. -/
lemma pre_evaluation {P Q : V} {E F G : D} (p : 𝟙_ V ⟶ Q) (f : E ⟶ F)
    (v : (H.obj Q).obj E ⟶ F) (w : (H.obj P).obj F ⟶ G)
    (hp : (H.map p).app E ≫ v = u.hom.app E ≫ f)
    (hn : (H.map (𝟙 P ⊗ₘ p)).app E ≫ (a P Q).hom.app E =
      (a P (𝟙_ V)).hom.app E ≫ (H.obj P).map ((H.map p).app E))
    (hu : (a P (𝟙_ V)).hom.app E ≫ (H.obj P).map (u.hom.app E) =
      (H.map (ρ_ P).hom).app E) :
    (H.map (𝟙 P ⊗ₘ p)).app E ≫
        MappingAssociativity.compositionEvaluation H a P Q v w =
      (H.map (ρ_ P).hom).app E ≫ (H.obj P).map f ≫ w := by
  unfold MappingAssociativity.compositionEvaluation
  rw [reassoc_of% hn, ← Functor.map_comp_assoc, hp, Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hu]

variable (R : D → D ⥤ V)
  (adj : ∀ E, MappingUnitLaws.parameterFunctor H E ⊣ R E)
open RepresentedMappingEnrichment

/-- Composition with the point of an ordinary arrow is the existing right
adjoint's map, on the entire mapping object. -/
lemma post_composition {E F G : D} (g : F ⟶ G)
    (hn : (H.map (arrow H u R adj g ⊗ₘ 𝟙 (hom R E F))).app E ≫
      (a (hom R F G) (hom R E F)).hom.app E =
      (a (𝟙_ V) (hom R E F)).hom.app E ≫
        (H.map (arrow H u R adj g)).app ((H.obj (hom R E F)).obj E))
    (hu : (a (𝟙_ V) (hom R E F)).hom.app E ≫
      u.hom.app ((H.obj (hom R E F)).obj E) =
        (H.map (λ_ (hom R E F)).hom).app E) :
    (λ_ (hom R E F)).inv ≫ arrow H u R adj g ▷ hom R E F ≫
      composition H a R adj E F G = (R E).map g := by
  rw [← Category.assoc]
  apply AdjunctionHomLaws.curry_pre_eq_of_evaluation (adj E)
    (compositionEvaluation H a R adj E F G)
    ((λ_ (hom R E F)).inv ≫ arrow H u R adj g ▷ hom R E F) ((R E).map g)
  change (H.map ((λ_ (hom R E F)).inv ≫ arrow H u R adj g ▷ hom R E F)).app E ≫
    compositionEvaluation H a R adj E F G =
      (H.map ((R E).map g)).app E ≫ evaluation H R adj E G
  have hp : (H.map (arrow H u R adj g)).app F ≫ evaluation H R adj F G =
      u.hom.app F ≫ g :=
    AdjunctionHomLaws.comparison_evaluation (adj F) (u.app F) g
  have he := post_evaluation H a u (arrow H u R adj g) g
    (evaluation H R adj E F) (evaluation H R adj F G) hp hn hu
  rw [H.map_comp, NatTrans.comp_app, Category.assoc]
  rw [← tensorHom_id (arrow H u R adj g) (hom R E F)]
  change (H.map (λ_ (hom R E F)).inv).app E ≫
    (H.map (arrow H u R adj g ⊗ₘ 𝟙 (hom R E F))).app E ≫
      compositionEvaluation H a R adj E F G = _
  change (H.map (arrow H u R adj g ⊗ₘ 𝟙 (hom R E F))).app E ≫
    compositionEvaluation H a R adj E F G =
      (H.map (λ_ (hom R E F)).hom).app E ≫ evaluation H R adj E F ≫ g at he
  rw [he]
  have hi : (H.map (λ_ (hom R E F)).inv).app E ≫
      (H.map (λ_ (hom R E F)).hom).app E = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← H.map_comp, Iso.inv_hom_id, H.map_id]
    rfl
  rw [← Category.assoc, ← Category.assoc, hi, Category.id_comp]
  exact ((adj E).counit.naturality g).symm

/-- Composition with an ordinary initial arrow is the transpose of precomposition
by its action, at arbitrary mapping-object parameters. -/
lemma pre_composition {E F G : D} (f : E ⟶ F)
    (hn : (H.map (𝟙 (hom R F G) ⊗ₘ arrow H u R adj f)).app E ≫
      (a (hom R F G) (hom R E F)).hom.app E =
      (a (hom R F G) (𝟙_ V)).hom.app E ≫
        (H.obj (hom R F G)).map ((H.map (arrow H u R adj f)).app E))
    (hu : (a (hom R F G) (𝟙_ V)).hom.app E ≫
      (H.obj (hom R F G)).map (u.hom.app E) =
        (H.map (ρ_ (hom R F G)).hom).app E) :
    (ρ_ (hom R F G)).inv ≫ hom R F G ◁ arrow H u R adj f ≫
      composition H a R adj E F G =
        (adj E).homEquiv (hom R F G) G
          ((H.obj (hom R F G)).map f ≫ evaluation H R adj F G) := by
  rw [← Category.assoc]
  conv_rhs => rw [← Category.id_comp ((adj E).homEquiv (hom R F G) G
    ((H.obj (hom R F G)).map f ≫ evaluation H R adj F G))]
  apply AdjunctionHomLaws.curry_pre_comparison_of_evaluation (adj E)
    (compositionEvaluation H a R adj E F G)
    ((H.obj (hom R F G)).map f ≫ evaluation H R adj F G)
    ((ρ_ (hom R F G)).inv ≫ hom R F G ◁ arrow H u R adj f) (𝟙 _)
  change (H.map ((ρ_ (hom R F G)).inv ≫ hom R F G ◁ arrow H u R adj f)).app E ≫
    compositionEvaluation H a R adj E F G =
      (H.map (𝟙 (hom R F G))).app E ≫
        (H.obj (hom R F G)).map f ≫ evaluation H R adj F G
  have hp : (H.map (arrow H u R adj f)).app E ≫ evaluation H R adj E F =
      u.hom.app E ≫ f :=
    AdjunctionHomLaws.comparison_evaluation (adj E) (u.app E) f
  have he := pre_evaluation H a u (arrow H u R adj f) f
    (evaluation H R adj E F) (evaluation H R adj F G) hp hn hu
  change (H.map (𝟙 (hom R F G) ⊗ₘ arrow H u R adj f)).app E ≫
    compositionEvaluation H a R adj E F G =
      (H.map (ρ_ (hom R F G)).hom).app E ≫
        (H.obj (hom R F G)).map f ≫ evaluation H R adj F G at he
  rw [H.map_comp, NatTrans.comp_app, Category.assoc,
    ← id_tensorHom (hom R F G) (arrow H u R adj f), he]
  have hi : (H.map (ρ_ (hom R F G)).inv).app E ≫
      (H.map (ρ_ (hom R F G)).hom).app E = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← H.map_comp, Iso.inv_hom_id, H.map_id]
    rfl
  rw [← Category.assoc, ← Category.assoc, hi, H.map_id]
  simp only [NatTrans.id_app, Category.id_comp]

end SerrePositivity.MappingWhiskering
