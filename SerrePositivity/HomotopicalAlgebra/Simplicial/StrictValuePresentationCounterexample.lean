module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.StrictValueDescentCounterexample
public import Mathlib.CategoryTheory.InducedCategory

/-! # Full presentation projection and local independence do not force fixed-value descent

All presentation values are small Kan complexes, all maps are weak equivalences,
and parallel maps agree after localization. The comparison to a changed-value
strict functor is a natural weak equivalence, whereas isomorphic descent is impossible.
-/

@[expose] public section
universe v vH uH
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.SimplicialModel.StrictValueObstruction
variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev Presentations := InducedCategory SSet.{v} value
abbrev diagram : Presentations.{v} ⥤ SSet.{v} := inducedFunctor value
abbrev projection : Presentations.{v} ⥤ Base := Codiscrete.functor (fun b => b.as)

def pointToValue (b : Base) : point ⟶ value.{v} b := by
  rcases b with ⟨b⟩
  cases b
  · exact 𝟙 _
  · exact SSet.stdSimplex.δ (1 : Fin 2) ≫ fromInterval

instance : (projection.{v}).Full where
  map_surjective {b c} _ :=
    ⟨InducedCategory.homMk (valueToPoint b ≫ pointToValue c), Subsingleton.elim _ _⟩

/-- This is a natural weak equivalence, and does not claim a natural isomorphism. -/
def changedValueComparison : diagram.{v} ⟶ projection.{v} ⋙ repair.{v} where
  app b := valueToPoint b
  naturality {_ _} _ := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

lemma changedValueComparison_weakEquivalence (b : Presentations.{v}) :
    weakEquivalences SSet.{v} (changedValueComparison.app b) := valueToPoint_weakEquivalence b

lemma diagram_map_weakEquivalence {b c : Presentations.{v}} (f : b ⟶ c) :
    weakEquivalences SSet.{v} (diagram.map f) := by
  apply (weakEquivalences SSet.{v}).of_postcomp _ (valueToPoint c)
    (valueToPoint_weakEquivalence c)
  have he : diagram.map f ≫ valueToPoint c = valueToPoint b :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  exact he.symm ▸ valueToPoint_weakEquivalence b

include hcof in
/-- A full projection and weakly invariant small Kan values do not yield isomorphic descent. -/
lemma no_isomorphic_descent (F : Base ⥤ SSet.{v}) :
    ¬ Nonempty (diagram.{v} ≅ projection.{v} ⋙ F) := by
  rintro ⟨e⟩
  exact no_fixed_value_lift hcof F (fun b => (e.app b).symm)

variable {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
  [L.IsLocalization (weakEquivalences SSet.{v})]

lemma parallel_maps_localize_equal {b c : Presentations.{v}} (f g : b ⟶ c) :
    L.map (diagram.map f) = L.map (diagram.map g) := by
  have : IsIso (L.map (valueToPoint c)) :=
    Localization.inverts L (weakEquivalences SSet.{v}) _ (valueToPoint_weakEquivalence c)
  apply (cancel_mono (L.map (valueToPoint c))).mp
  rw [← L.map_comp, ← L.map_comp]
  exact congrArg L.map (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)

instance changedValueComparison_localized_isIso :
    IsIso (Functor.whiskerRight (changedValueComparison.{v}) L) := by
  have : ∀ b, IsIso ((Functor.whiskerRight (changedValueComparison.{v}) L).app b) :=
    fun b => Localization.inverts L (weakEquivalences SSet.{v}) _
      (changedValueComparison_weakEquivalence b)
  exact NatIso.isIso_of_isIso_app _

end SerrePositivity.SimplicialModel.StrictValueObstruction
