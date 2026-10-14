module

public import SerrePositivity.CategoryTheory.Monoidal.ReverseComposition

/-! # 豊穣構造の移送の合成と単位の比較 -/

@[expose] public section

universe v₁ v₂ u₁ u₂ u₃

noncomputable section

namespace SerrePositivity.TransportEnrichmentComparisons

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Functor.LaxMonoidal

variable {V : Type u₁} {W : Type u₂} [Category.{v₁} V] [Category.{v₂} W]
  [MonoidalCategory V] [MonoidalCategory W]
  (F : V ⥤ W) (C : Type u₃) [EnrichedCategory V C]

section

variable [F.LaxMonoidal]

/-- lax monoidal関手で移した豊穣構造を元の対象型で扱う。 -/
@[instance_reducible]
def category : EnrichedCategory W C :=
  inferInstanceAs (EnrichedCategory W (TransportEnrichment F C))

/-- 移した豊穣構造の単位と指定した射の一致。 -/
def identityLaw (X : C) (k : 𝟙_ W ⟶ F.obj (X ⟶[V] X)) : Prop :=
  (category F C).id X = k

/-- 元の単位と関手の単位比較から、移送後の単位の一致を得る。 -/
lemma identity_eq (X : C) (e : 𝟙_ V ⟶ (X ⟶[V] X))
    (he : eId V X = e) (k : 𝟙_ W ⟶ F.obj (X ⟶[V] X))
    (hk : ε F ≫ F.map e = k) : identityLaw F C X k := by
  change ε F ≫ F.map (eId V X) = k
  rw [he]
  exact hk

end

variable [BraidedCategory V] [BraidedCategory W] [F.LaxBraided]

/-- 逆順の合成から移した豊穣構造の合成の具体式。 -/
def reverseCompositionLaw (X Y Z : C) (m : (Y ⟶[V] Z) ⊗ (X ⟶[V] Y) ⟶ (X ⟶[V] Z)) :
    Prop :=
  (category F C).comp X Y Z =
    (β_ (F.obj (X ⟶[V] Y)) (F.obj (Y ⟶[V] Z))).hom ≫
      μ F (Y ⟶[V] Z) (X ⟶[V] Y) ≫ F.map m

/-- 交換で逆順にした合成の移送は、交換・関手の比較・元の合成の順に計算できる。 -/
lemma reverse_composition (X Y Z : C)
    (m : (Y ⟶[V] Z) ⊗ (X ⟶[V] Y) ⟶ (X ⟶[V] Z))
    (hm : eComp V X Y Z = ReverseComposition.reverse m) :
    reverseCompositionLaw F C X Y Z m := by
  change μ F _ _ ≫ F.map (eComp V X Y Z) = _
  rw [hm, ReverseComposition.reverse, F.map_comp, ← Category.assoc, Functor.LaxBraided.braided]
  exact Category.assoc _ _ _

end SerrePositivity.TransportEnrichmentComparisons
