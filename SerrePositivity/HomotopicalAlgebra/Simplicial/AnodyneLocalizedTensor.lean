module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct

/-! # Cartesian tensor preserves every anodyne-localized equivalence

The tensor functors preserve the actual anodyne generators and their
closure. The localization universal property then handles every inverted
map, without a model structure in the value universe.
-/

@[expose] public section
universe v uH vH
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.SimplicialModel.AnodyneHomotopy
variable {X Y : SSet.{v}} (f : X ⟶ Y) (hf : IsIso (anodyneQ.map f)) (A : SSet.{v})
  {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hf hL in
lemma whiskerLeft_image_isIso : IsIso (L.map (A ◁ f)) := by
  let T := tensorLeft A ⋙ L
  have hT : SSet.anodyneExtensions.IsInvertedBy T := by
    intro U V g hg
    exact hL _ (hg.whiskerLeft A)
  exact map_isIso_of_anodyneQ_isIso T hT f hf

include hf hL in
lemma whiskerRight_image_isIso : IsIso (L.map (f ▷ A)) := by
  let T := tensorRight A ⋙ L
  have hT : SSet.anodyneExtensions.IsInvertedBy T := by
    intro U V g hg
    exact hL _ (hg.whiskerRight A)
  exact map_isIso_of_anodyneQ_isIso T hT f hf

include hf in
lemma whiskerLeft_anodyneQ_isIso : IsIso (anodyneQ.map (A ◁ f)) :=
  whiskerLeft_image_isIso f hf A anodyneQ (Localization.inverts anodyneQ SSet.anodyneExtensions)

include hf in
lemma whiskerRight_anodyneQ_isIso : IsIso (anodyneQ.map (f ▷ A)) :=
  whiskerRight_image_isIso f hf A anodyneQ (Localization.inverts anodyneQ SSet.anodyneExtensions)

end SerrePositivity.SimplicialModel.AnodyneHomotopy
