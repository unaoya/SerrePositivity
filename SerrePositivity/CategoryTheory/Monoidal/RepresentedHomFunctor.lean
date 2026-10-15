module

public import SerrePositivity.CategoryTheory.Monoidal.MappingWhiskering

/-! # The Hom functor of a represented ordinary enrichment

The proof is performed with abstract action and adjunction data. Applications
need not normalize concrete chosen adjunction records in the kernel.
-/

@[expose] public section
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

end SerrePositivity.RepresentedHomFunctor
