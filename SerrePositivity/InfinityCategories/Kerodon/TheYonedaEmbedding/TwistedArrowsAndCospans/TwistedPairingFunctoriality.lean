module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedPairingNerve
/-! 同じ元のpairingの添字表示・前合成・係数移送の厳密な照合。 -/

@[expose] public section
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

lemma twistedPairingNerveMap_precomp {J I C : Type u} [Category.{u} J] [Category.{u} I]
    [Category.{u} C] (H : J ⥤ I) (A : I ⥤ Cᵒᵖ) (B : I ⥤ C)
    (h : ∀ i, (A.obj i).unop ⟶ B.obj i)
    (hh : ∀ {i j} (f : i ⟶ j), (A.map f).unop ≫ h i ≫ B.map f = h j) :
    nerveMap H ≫ twistedPairingNerveMap A B h hh =
      twistedPairingNerveMap (H ⋙ A) (H ⋙ B) (fun i => h (H.obj i))
        (fun {_ _} f => hh (H.map f)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro σ
  rfl
lemma twistedPairingNerveMap_congr {I C : Type u} [Category.{u} I] [Category.{u} C]
    {A A' : I ⥤ Cᵒᵖ} {B B' : I ⥤ C} (ha : A = A') (hb : B = B')
    (h : ∀ i, (A.obj i).unop ⟶ B.obj i) (h' : ∀ i, (A'.obj i).unop ⟶ B'.obj i)
    (hh : ∀ {i j} (f : i ⟶ j), (A.map f).unop ≫ h i ≫ B.map f = h j)
    (hh' : ∀ {i j} (f : i ⟶ j), (A'.map f).unop ≫ h' i ≫ B'.map f = h' j)
    (hv : ∀ i, HEq (h i) (h' i)) :
    twistedPairingNerveMap A B h hh = twistedPairingNerveMap A' B' h' hh' := by
  subst A' B'
  have he : h = h' := funext (fun i => eq_of_heq (hv i))
  subst h'
  rfl
end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
end
