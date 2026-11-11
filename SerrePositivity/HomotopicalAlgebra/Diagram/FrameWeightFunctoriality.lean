module

public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameWeightRealization
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Functoriality of actual frame-weight realization in the source frames

The pointwise cosimplicial Hom is contravariant in frames. Mates under
the specified ordinary adjunctions give the actual covariant realization
maps, including their identity, composition and adjunction compatibility.
-/

@[expose] public section
universe w u
noncomputable section
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.DiagramModel.FrameWeightRealization
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{w} C]
  [HasColimitsOfSize.{w, w} C]

abbrev homFamily : (K ⥤ SimplexCategory ⥤ C)ᵒᵖ ⥤ C ⥤ Kᵒᵖ ⥤ SSet.{w} :=
  Functor.opHom K (SimplexCategory ⥤ C) ⋙
    (Functor.whiskeringRight Kᵒᵖ (SimplexCategory ⥤ C)ᵒᵖ (C ⥤ SSet.{w})).obj
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor ⋙ flipFunctor Kᵒᵖ C SSet.{w}

def map {A B : K ⥤ SimplexCategory ⥤ C} (a : A ⟶ B) : functor K A ⟶ functor K B :=
  (conjugateEquiv (adjunction K B) (adjunction K A)).symm ((homFamily K).map a.op)

lemma map_id (A : K ⥤ SimplexCategory ⥤ C) : map K (𝟙 A) = 𝟙 (functor K A) := by
  simp [map]

lemma map_comp {A B E : K ⥤ SimplexCategory ⥤ C} (a : A ⟶ B) (b : B ⟶ E) :
    map K (a ≫ b) = map K a ≫ map K b := by
  unfold map
  rw [op_comp, (homFamily K).map_comp,
    ← conjugateEquiv_symm_comp (adjunction K E) (adjunction K B) (adjunction K A)]

/-- Objects are the original chosen Kan realizations, not replacement realizations. -/
def family : (K ⥤ SimplexCategory ⥤ C) ⥤ (Kᵒᵖ ⥤ SSet.{w}) ⥤ C where
  obj := functor K
  map := map K
  map_id := map_id K
  map_comp := map_comp K

lemma homEquiv_frame_naturality {A B : K ⥤ SimplexCategory ⥤ C} (a : A ⟶ B)
    (W : Kᵒᵖ ⥤ SSet.{w}) (Y : C) (t : (functor K B).obj W ⟶ Y) :
    (adjunction K A).homEquiv W Y ((map K a).app W ≫ t) =
      (adjunction K B).homEquiv W Y t ≫ ((homFamily K).map a.op).app Y := by
  rw [(adjunction K A).homEquiv_unit, (adjunction K B).homEquiv_unit,
    (hom K A).map_comp, ← Category.assoc]
  unfold map
  rw [← unit_conjugateEquiv_symm (adjunction K B) (adjunction K A)
    ((homFamily K).map a.op) W]
  rw [Category.assoc, ← NatTrans.naturality, ← Category.assoc]

end SerrePositivity.DiagramModel.FrameWeightRealization
