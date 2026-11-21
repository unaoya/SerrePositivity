module

public import SerrePositivity.CategoryTheory.Enriched.OfAdjunctionData

/-!
# 対象ごとの随伴による豊穣 Hom の関手性
-/

/-! # Evaluation of composition with an ordinary arrow

One ordinary arrow and one arbitrary mapping-object parameter suffice to recover
mapping functoriality. These laws do not assume that unit-valued points detect
all morphisms of the enriching category.
-/

@[expose] public section MappingWhiskering
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

section Enriched
variable [BraidedCategory V]
  (hl : ∀ E F, leftUnitLaw H a u R adj E F)
  (hr : ∀ E F, rightUnitLaw H a u R adj E F)
  (ha : ∀ E F G K, associativityLaw H a R adj E F G K)
  (hi : ∀ E, arrowIdentityLaw H u R adj E)
  (hc : ∀ {E F G} (f : E ⟶ F) (g : F ⟶ G), arrowCompositionLaw H a u R adj f g)

lemma enriched_post {E F G : D} (g : F ⟶ G)
    (hn : (H.map (arrow H u R adj g ⊗ₘ 𝟙 (hom R E F))).app E ≫
      (a (hom R F G) (hom R E F)).hom.app E =
      (a (𝟙_ V) (hom R E F)).hom.app E ≫
        (H.map (arrow H u R adj g)).app ((H.obj (hom R E F)).obj E))
    (hu : (a (𝟙_ V) (hom R E F)).hom.app E ≫
      u.hom.app ((H.obj (hom R E F)).obj E) = (H.map (λ_ (hom R E F)).hom).app E) :
    let : EnrichedOrdinaryCategory V D := ordinaryCategory H a u R adj hl hr ha hi hc
    eHomWhiskerLeft V E g = (R E).map g := by
  let : EnrichedOrdinaryCategory V D := ordinaryCategory H a u R adj hl hr ha hi hc
  change (ρ_ (hom R E F)).inv ≫ hom R E F ◁ arrow H u R adj g ≫
    (β_ _ _).hom ≫ composition H a R adj E F G = _
  rw [BraidedCategory.braiding_naturality_right_assoc,
    ← Category.assoc, rightUnitor_inv_braiding]
  exact post_composition H a u R adj g hn hu

lemma enriched_pre {E F G : D} (f : E ⟶ F)
    (hn : (H.map (𝟙 (hom R F G) ⊗ₘ arrow H u R adj f)).app E ≫
      (a (hom R F G) (hom R E F)).hom.app E =
      (a (hom R F G) (𝟙_ V)).hom.app E ≫
        (H.obj (hom R F G)).map ((H.map (arrow H u R adj f)).app E))
    (hu : (a (hom R F G) (𝟙_ V)).hom.app E ≫
      (H.obj (hom R F G)).map (u.hom.app E) = (H.map (ρ_ (hom R F G)).hom).app E) :
    let : EnrichedOrdinaryCategory V D := ordinaryCategory H a u R adj hl hr ha hi hc
    eHomWhiskerRight V f G = (adj E).homEquiv (hom R F G) G
      ((H.obj (hom R F G)).map f ≫ evaluation H R adj F G) := by
  let : EnrichedOrdinaryCategory V D := ordinaryCategory H a u R adj hl hr ha hi hc
  change (λ_ (hom R F G)).inv ≫ arrow H u R adj f ▷ hom R F G ≫
    (β_ _ _).hom ≫ composition H a R adj E F G = _
  rw [BraidedCategory.braiding_naturality_left_assoc,
    ← Category.assoc, leftUnitor_inv_braiding]
  exact pre_composition H a u R adj f hn hu
end Enriched

end SerrePositivity.MappingWhiskering
end

end MappingWhiskering


/-! # The Hom functor of a represented ordinary enrichment

The proof is performed with abstract action and adjunction data. Applications
need not normalize concrete chosen adjunction records in the kernel.
-/

@[expose] public section RepresentedHomFunctor
universe v₁ v₂ u₁ u₂

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory Opposite
namespace SerrePositivity.RepresentedHomFunctor
open RepresentedMappingEnrichment
variable {V : Type u₁} {D : Type u₂} [Category.{v₁} V] [Category.{v₂} D]
  [MonoidalCategory V] [BraidedCategory V]
  (H : V ⥤ D ⥤ D) (a : ∀ P Q : V, H.obj (P ⊗ Q) ≅ H.obj Q ⋙ H.obj P)
  (u : H.obj (𝟙_ V) ≅ 𝟭 D) (R : D → D ⥤ V)
  (adj : ∀ E, MappingUnitLaws.parameterFunctor H E ⊣ R E)
  (hl : ∀ E F, leftUnitLaw H a u R adj E F)
  (hr : ∀ E F, rightUnitLaw H a u R adj E F)
  (ha : ∀ E F G K, associativityLaw H a R adj E F G K)
  (hi : ∀ E, arrowIdentityLaw H u R adj E)
  (hc : ∀ {E F G} (f : E ⟶ F) (g : F ⟶ G), arrowCompositionLaw H a u R adj f g)
  (hL : ∀ {P P' : V} (p : P ⟶ P') (Q : V) (E : D),
    (H.map (p ⊗ₘ 𝟙 Q)).app E ≫ (a P' Q).hom.app E =
      (a P Q).hom.app E ≫ (H.map p).app ((H.obj Q).obj E))
  (hR : ∀ (P : V) {Q Q' : V} (q : Q ⟶ Q') (E : D),
    (H.map (𝟙 P ⊗ₘ q)).app E ≫ (a P Q').hom.app E =
      (a P Q).hom.app E ≫ (H.obj P).map ((H.map q).app E))
  (huL : ∀ (P : V) (E : D), (a (𝟙_ V) P).hom.app E ≫
    u.hom.app ((H.obj P).obj E) = (H.map (λ_ P).hom).app E)
  (huR : ∀ (P : V) (E : D), (a P (𝟙_ V)).hom.app E ≫
    (H.obj P).map (u.hom.app E) = (H.map (ρ_ P).hom).app E)
  (B : Dᵒᵖ ⥤ D ⥤ V) (e : ∀ E, R E ≅ B.obj (op E))
  (hn : ∀ {E F : D} (f : E ⟶ F) (X : V) (G : D) (g : (H.obj X).obj F ⟶ G),
    (adj E).homEquiv X G ((H.obj X).map f ≫ g) ≫ (e E).hom.app G =
      (adj F).homEquiv X G g ≫ (e F).hom.app G ≫ (B.map f.op).app G)

/-- 指定した前合成と後合成から、豊穣 Hom と写像対象の関手の自然同型を作る。 -/
def homFunctorIso :
    let : EnrichedOrdinaryCategory V D := ordinaryCategory H a u R adj hl hr ha hi hc
    eHomFunctor V D ≅ B := by
  let : EnrichedOrdinaryCategory V D := ordinaryCategory H a u R adj hl hr ha hi hc
  have hpost (E : D) {F G : D} (g : F ⟶ G) : eHomWhiskerLeft V E g = (R E).map g :=
    MappingWhiskering.enriched_post H a u R adj hl hr ha hi hc g
      (hL _ _ _) (huL _ _)
  have hpre {E F : D} (f : E ⟶ F) (G : D) :
      eHomWhiskerRight V f G ≫ (e E).hom.app G = (e F).hom.app G ≫ (B.map f.op).app G := by
    rw [MappingWhiskering.enriched_pre H a u R adj hl hr ha hi hc f (hR _ _ _) (huR _ _)]
    have he : (adj F).homEquiv (hom R F G) G (evaluation H R adj F G) = 𝟙 _ := by
      exact ((adj F).homEquiv _ G).eq_symm_apply.mp ((adj F).homEquiv_symm_id G).symm
    simpa only [he, Category.id_comp] using hn f (hom R F G) G (evaluation H R adj F G)
  refine NatIso.ofComponents (fun E ↦ NatIso.ofComponents (fun F ↦ (e E.unop).app F) ?_) ?_
  · intro F G g
    change eHomWhiskerLeft V E.unop g ≫ (e E.unop).hom.app G =
      (e E.unop).hom.app F ≫ (B.obj E).map g
    rw [hpost]
    exact (e E.unop).hom.naturality g
  · intro E F f
    apply NatTrans.ext
    funext G
    exact hpre f.unop G

/-- A parametrized adjunction supplies the contravariant naturality automatically.
閉じた V 加群からの構成（`OfAction`）に置き換える予定。使う側が移った後に消す。
-/
def homFunctorIso_ofParametrized
    (adj₂ : H.flip ⊣₂ B)
    (hl' : ∀ E F, leftUnitLaw H a u (fun E ↦ B.obj (op E)) adj₂.adj E F)
    (hr' : ∀ E F, rightUnitLaw H a u (fun E ↦ B.obj (op E)) adj₂.adj E F)
    (ha' : ∀ E F G K, associativityLaw H a (fun E ↦ B.obj (op E)) adj₂.adj E F G K)
    (hi' : ∀ E, arrowIdentityLaw H u (fun E ↦ B.obj (op E)) adj₂.adj E)
    (hc' : ∀ {E F G} (f : E ⟶ F) (g : F ⟶ G),
      arrowCompositionLaw H a u (fun E ↦ B.obj (op E)) adj₂.adj f g) :
    let : EnrichedOrdinaryCategory V D := ordinaryCategory H a u
      (fun E ↦ B.obj (op E)) adj₂.adj hl' hr' ha' hi' hc'
    eHomFunctor V D ≅ B := by
  apply homFunctorIso H a u (fun E ↦ B.obj (op E)) adj₂.adj
    hl' hr' ha' hi' hc' hL hR huL huR B (fun _ ↦ Iso.refl _)
  intro E F f X G g
  simp only [Iso.refl_hom, NatTrans.id_app, Category.comp_id, Category.id_comp]
  change adj₂.homEquiv ((H.flip.map f).app X ≫ g) =
    adj₂.homEquiv g ≫ (B.map f.op).app G
  exact adj₂.homEquiv_naturality_one (X₁ := E) (Y₁ := F) (X₂ := X) (X₃ := G) f g

end SerrePositivity.RepresentedHomFunctor
end

end RepresentedHomFunctor
