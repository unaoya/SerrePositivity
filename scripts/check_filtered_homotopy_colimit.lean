import SerrePositivity.HomotopicalAlgebra.Diagram.FilteredHomotopyColimit
import Lean.Util.CollectAxioms

noncomputable section
universe w v u vD uD vH uH
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.DiagramModel

variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

local instance : HasColimitsOfSize.{w, w} C :=
  SerrePositivity.Smith.locallyPresentable_hasColimits (C := C)

-- A single bound works for every larger regular cardinal and every small
-- indexing category filtered at that cardinal, with no cofibrancy input.
example : ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
    ∀ (μ : Cardinal.{w}) [Fact μ.IsRegular], κ ≤ μ →
      ∀ (K : Type w) [SmallCategory K] [IsCardinalFiltered K μ] (F : K ⥤ C),
        weakEquivalences C ((HomotopyColimit.comparison K I J).app F) :=
  HomotopyColimit.exists_filtered_comparison I J

-- The hocolim functor itself preserves every objectwise weak equivalence,
-- for arbitrary small diagram shapes, not just filtered ones.
example (K : Type w) [SmallCategory K] {F G : K ⥤ C} (f : F ⟶ G)
    (hf : ∀ k, weakEquivalences C (f.app k)) :
    weakEquivalences C ((HomotopyColimit.functor K I J).map f) :=
  HomotopyColimit.map_weakEquivalence K I J f hf

-- Cofibrant projective diagrams also compute hocolim without filteredness.
example (K : Type w) [SmallCategory K] (F : K ⥤ C)
    (hF : let := Projective.modelCategory K I J; IsCofibrant F) :
    weakEquivalences C ((HomotopyColimit.comparison K I J).app F) :=
  HomotopyColimit.comparison_weakEquivalence_of_cofibrant K I J F hF

-- After arbitrary ordinary localizations, the actual constructed hocolim
-- computes every left derived colimit by a natural isomorphism of functors.
example (K : Type w) [SmallCategory K] {D : Type uD} [Category.{vD} D]
    {H : Type uH} [Category.{vH} H]
    (Q : (K ⥤ C) ⥤ D) [Q.IsLocalization (Projective.objectwise K (weakEquivalences C))]
    (L : C ⥤ H) [L.IsLocalization (weakEquivalences C)] (LF : D ⥤ H)
    (α : Q ⋙ LF ⟶ (colim : (K ⥤ C) ⥤ C) ⋙ L)
    [LF.IsLeftDerivedFunctor α (Projective.objectwise K (weakEquivalences C))] :
    Q ⋙ LF ≅ HomotopyColimit.functor K I J ⋙ L :=
  HomotopyColimit.computesDerivedIso K I J Q L LF α

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyColimit,
    `SerrePositivity.HomotopicalAlgebra.Diagram.ColimitWeakEquivalence,
    `SerrePositivity.HomotopicalAlgebra.Diagram.FilteredHomotopyColimit]
  let mut count : Nat := 0
  let mut seen : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless seen.contains mod do seen := seen.push mod
  for mod in expected do
    unless seen.contains mod do throwError "Module not audited: {mod}"
  logInfo m!"Filtered homotopy colimit audit passed: {count} declarations in {seen.size} modules."
