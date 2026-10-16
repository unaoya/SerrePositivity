module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanTestDetection
public import Mathlib.AlgebraicTopology.SimplicialSet.Nonempty

/-! # Anodyne localization reflects nonemptiness of vertices

The empty simplicial set is a Kan test. No simplicial model structure is used.
-/

@[expose] public section
universe v
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.AnodyneNonempty

abbrev empty : SSet.{v} := (Functor.const SimplexCategoryᵒᵖ).obj PEmpty

lemma empty_kan : SSet.modelCategoryQuillen.J.rlp (terminal.from empty.{v}) := by
  apply (SSet.modelCategoryQuillen.fibration_iff _).mp
  apply SSet.KanComplex.iff.mpr
  intro n i f _
  obtain ⟨j, hj⟩ := exists_ne i
  exact PEmpty.elim ((f j hj).app (Opposite.op (SimplexCategory.mk 0))
    (SSet.stdSimplex.obj₀Equiv.symm 0))

lemma nonempty_of_localized_isIso {X Y : SSet.{v}} (f : X ⟶ Y)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map f)) (hY : Y.Nonempty) : X.Nonempty := by
  by_contra hX
  have hs := (KanTestDetection.tests_of_anodyneQ_isIso f hf empty empty_kan).surjective
  obtain ⟨g, _⟩ := hs
    (HomotopyClasses.mk ((SSet.isInitialOfNotNonempty hX).to empty))
  obtain ⟨g, rfl⟩ := Quot.exists_rep g
  exact PEmpty.elim (g.app (Opposite.op (SimplexCategory.mk 0)) (Classical.choice hY))

lemma nonempty_iff_of_localized_isIso {X Y : SSet.{v}} (f : X ⟶ Y)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map f)) : X.Nonempty ↔ Y.Nonempty :=
  ⟨fun hX => ⟨f.app _ (Classical.choice hX)⟩, nonempty_of_localized_isIso f hf⟩

end SerrePositivity.SimplicialModel.AnodyneNonempty
