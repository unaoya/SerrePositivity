import SerrePositivity.HomotopicalAlgebra.Diagram.YonedaHomotopyWeight
import SerrePositivity.HomotopicalAlgebra.Diagram.QuillenColimitComparison
import Lean.Util.CollectAxioms

noncomputable section
universe w v u v' u'
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.DiagramModel

section Ordinary
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [HasColimitsOfSize.{w, w} C] (X : C)

example : colimit (YonedaWeights.family K X) ≅ (Functor.const Kᵒᵖ).obj X :=
  YonedaWeights.colimitIso K X

example (l : Kᵒᵖ) : YonedaWeights.family K X ⋙ (evaluation Kᵒᵖ C).obj l ≅
    (evaluationLeftAdjoint C l.unop).obj X := YonedaWeights.evaluationIso K X l

example (k : K) : (YonedaWeights.family K X).obj k ≅
    (evaluationLeftAdjoint C (Opposite.op k)).obj X := YonedaWeights.freeWeightIso K X k
end Ordinary

variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

-- No projective cofibrancy of the constant diagram is assumed.
example (X : C) : let := Projective.modelCategory Kᵒᵖ I J
    IsCofibrant (YonedaHomotopyWeight.weight K I J X) :=
  YonedaHomotopyWeight.weight_isCofibrant K I J X

example (X : C) [IsCofibrant X] : let := Projective.modelCategory Kᵒᵖ I J
    weakEquivalences (Kᵒᵖ ⥤ C) (YonedaHomotopyWeight.augmentation K I J X) :=
  YonedaHomotopyWeight.augmentation_weakEquivalence K I J X

-- Source and target Hom universes need not coincide with the diagram universe.
example {D : Type u'} [Category.{v'} D] [ModelCategory D] [IsLocallyPresentable.{w} D]
    (I' J' : MorphismProperty D)
    [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I' J']
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [SerrePositivity.Quillen.IsLeftQuillen L]
    (F : K ⥤ C) (hF : ∀ k, IsCofibrant (F.obj k))
    (hFL : let := Projective.modelCategory K I' J'; IsCofibrant (F ⋙ L)) :
    weakEquivalences D (L.map ((HomotopyColimit.comparison K I J).app F)) :=
  QuillenColimitComparison.map_homotopyColimit_comparison_weakEquivalence K I J I' J' adj F hF hFL

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Quillen.CofibrantObjects,
    `SerrePositivity.HomotopicalAlgebra.Diagram.PostcompositionQuillen,
    `SerrePositivity.HomotopicalAlgebra.Diagram.YonedaWeights,
    `SerrePositivity.HomotopicalAlgebra.Diagram.PointwiseColimitComparison,
    `SerrePositivity.HomotopicalAlgebra.Diagram.YonedaHomotopyWeight,
    `SerrePositivity.HomotopicalAlgebra.Diagram.QuillenColimitComparison]
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
  logInfo m!"Yoneda homotopy weight audit passed: {count} declarations in {seen.size} modules."
