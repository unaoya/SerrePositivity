module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanMonoStrictExtension

/-! # Prescribed Kan maps extend after an actual pushout of a localized mono

This proves strict extension and the surjective half of the Kan class
test. It does not assert injectivity or invertibility of the pushout map.
-/

@[expose] public section
universe v
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.KanMonoPushoutExtension
open HomotopyClasses
variable {A B C P K : SSet.{v}} (i : A ⟶ B) [Mono i]
  (j : A ⟶ C) (u : B ⟶ P) (g : C ⟶ P) (sq : IsPushout i j u g)
  (hi : IsIso (AnodyneHomotopy.anodyneQ.map i))
  (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))

include sq hi hK in
lemma exists_extension (a : C ⟶ K) : ∃ b : P ⟶ K, g ≫ b = a := by
  obtain ⟨e, he⟩ := KanMonoStrictExtension.exists_extension i hK hi (j ≫ a)
  exact ⟨sq.desc e a he, sq.inr_desc e a he⟩

include sq hi hK in
lemma pre_surjective : Function.Surjective (pre g (K := K)) := by
  intro x
  obtain ⟨a, rfl⟩ := Quot.exists_rep x
  obtain ⟨b, hb⟩ := exists_extension i j u g sq hi hK a
  exact ⟨mk b, congrArg mk hb⟩

end SerrePositivity.SimplicialModel.KanMonoPushoutExtension
