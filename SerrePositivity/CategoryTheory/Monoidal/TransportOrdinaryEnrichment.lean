module

public import SerrePositivity.CategoryTheory.Monoidal.TransportEnrichmentComparisons
public import SerrePositivity.CategoryTheory.Monoidal.LaxPointHom
public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
public import Mathlib.CategoryTheory.Whiskering

/-! # 単位からの射の同値による通常の豊穣圏の移送 -/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

namespace SerrePositivity.TransportOrdinaryEnrichment

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Functor.LaxMonoidal

variable {V : Type u₁} {W : Type u₂} [Category.{v₁} V] [Category.{v₂} W]
  [MonoidalCategory V] [MonoidalCategory W] (F : V ⥤ W) [F.LaxMonoidal]
  (C : Type u₃) [Category.{v₃} C] [EnrichedOrdinaryCategory V C]
  (t : ∀ X : V, (𝟙_ V ⟶ X) ≃ (𝟙_ W ⟶ F.obj X))
  (ht : ∀ X (f : 𝟙_ V ⟶ X), t X f = LaxPointHom.map F f)

/-- 単位からの射の同値を使って既存の圏構造も豊穣構造とともに移す。 -/
@[instance_reducible]
def ordinaryCategory : EnrichedOrdinaryCategory W C where
  toEnrichedCategory := TransportEnrichmentComparisons.category F C
  homEquiv {X Y} := (eHomEquiv V).trans (t (X ⟶[V] Y))
  homEquiv_id X := by
    change t (X ⟶[V] X) (eHomEquiv V (𝟙 X)) = ε F ≫ F.map (eId V X)
    rw [eHomEquiv_id, ht]
    rfl
  homEquiv_comp {X Y Z} f g := by
    change t (X ⟶[V] Z) (eHomEquiv V (f ≫ g)) =
      (λ_ (𝟙_ W)).inv ≫
        (t (X ⟶[V] Y) (eHomEquiv V f) ⊗ₘ t (Y ⟶[V] Z) (eHomEquiv V g)) ≫
          μ F (X ⟶[V] Y) (Y ⟶[V] Z) ≫ F.map (eComp V X Y Z)
    rw [ht, ht, ht, eHomEquiv_comp]
    exact (LaxPointHom.composition F (eHomEquiv V f) (eHomEquiv V g) (eComp V X Y Z)).symm

lemma whiskerRight_map {X X' : C} (f : X ⟶ X') (Y : C) :
    let : EnrichedOrdinaryCategory W C := ordinaryCategory F C t ht
    eHomWhiskerRight W f Y = F.map (eHomWhiskerRight V f Y) := by
  let : EnrichedOrdinaryCategory W C := ordinaryCategory F C t ht
  change (λ_ (F.obj (X' ⟶[V] Y))).inv ≫
    t (X ⟶[V] X') (eHomEquiv V f) ▷ F.obj (X' ⟶[V] Y) ≫
      μ F _ _ ≫ F.map (eComp V X X' Y) = _
  rw [ht]
  exact LaxPointHom.left_action F _ _

lemma whiskerLeft_map (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    let : EnrichedOrdinaryCategory W C := ordinaryCategory F C t ht
    eHomWhiskerLeft W X g = F.map (eHomWhiskerLeft V X g) := by
  let : EnrichedOrdinaryCategory W C := ordinaryCategory F C t ht
  change (ρ_ (F.obj (X ⟶[V] Y))).inv ≫
    F.obj (X ⟶[V] Y) ◁ t (Y ⟶[V] Y') (eHomEquiv V g) ≫
      μ F _ _ ≫ F.map (eComp V X Y Y') = _
  rw [ht]
  exact LaxPointHom.right_action F _ _

def homFunctorIso :
    let : EnrichedOrdinaryCategory W C := ordinaryCategory F C t ht
    eHomFunctor V C ⋙ (CategoryTheory.Functor.whiskeringRight C V W).obj F ≅
      eHomFunctor W C := by
  let : EnrichedOrdinaryCategory W C := ordinaryCategory F C t ht
  refine NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun Y ↦ Iso.refl _) ?_) ?_
  · rename_i X
    intro Y Y' g
    change F.map (eHomWhiskerLeft V X.unop g) ≫ 𝟙 _ = 𝟙 _ ≫ eHomWhiskerLeft W X.unop g
    rw [whiskerLeft_map F C t ht, Category.id_comp, Category.comp_id]
  · intro X X' f
    apply NatTrans.ext
    funext Y
    change F.map (eHomWhiskerRight V f.unop Y) ≫ 𝟙 _ = 𝟙 _ ≫ eHomWhiskerRight W f.unop Y
    rw [whiskerRight_map F C t ht, Category.id_comp, Category.comp_id]

end SerrePositivity.TransportOrdinaryEnrichment
