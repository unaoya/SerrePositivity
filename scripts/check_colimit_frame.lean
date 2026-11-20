import SerrePositivity.HomotopicalAlgebra.Diagram.ColimitMapComparison
import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.AdjunctionHom
import Lean.Util.CollectAxioms

noncomputable section
universe w v u vD uD
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
  (cosimplicialHom adjunctionHomIso)
open SerrePositivity.DiagramModel

-- Ordinary adjunctions with independent Hom universes induce actual
-- simplicial isomorphisms, without any model structures.
example {C : Type u} [Category.{v} C] {D : Type uD} [Category.{vD} D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (A : SimplexCategory ⥤ C) :
    cosimplicialHom (A ⋙ L) ⋙ SSet.uliftFunctor.{v,vD} ≅
      R ⋙ cosimplicialHom A ⋙ SSet.uliftFunctor.{vD,v} := adjunctionHomIso adj A

variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

-- No enrichment or extra latching hypotheses are inputs to these consumers.
example (F : K ⥤ C) :
    reedyLeft simplex (cofibrations C) (initial.to ((ColimitFrame.frame K I J).obj F)) :=
  ColimitFrame.reedyCofibrant K I J F

example (F : K ⥤ C) (n : SimplexCategory) :
    weakEquivalences C (((ColimitFrame.augmentation K I J).app F).app n) :=
  ColimitFrame.augmentation_weakEquivalence K I J F n

example (F : K ⥤ C) (Y : C) [IsFibrant Y] :
    SSet.KanComplex ((cosimplicialHom ((ColimitFrame.frame K I J).obj F)).obj Y) :=
  ColimitFrame.hom_kanComplex K I J F Y

variable (cof : MorphismProperty.FunctorialFactorizationData
    (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData
    (trivialCofibrations C) (fibrations C))

-- Both maps are actual natural transformations in the input diagram AND Y.
example : (HomotopyColimit.functor K I J).op ⋙ chosenResolutionHom cof fib ⟶
    ColimitMapComparison.middle K I J cof fib := ColimitMapComparison.left K I J cof fib
example : ColimitMapComparison.frameHom K I J fib ⟶
    ColimitMapComparison.middle K I J cof fib := ColimitMapComparison.right K I J cof fib

example (F : (K ⥤ C)ᵒᵖ) (Y : C) :
    SSet.KanComplex (((ColimitMapComparison.middle K I J cof fib).obj F).obj Y) :=
  ColimitMapComparison.middle_kanComplex K I J cof fib F Y

example (F : (K ⥤ C)ᵒᵖ) (Y : C) :
    SSet.KanComplex (((ColimitMapComparison.diagramHom K I J fib).obj F).obj Y) :=
  ColimitMapComparison.diagramHom_kanComplex K I J fib F Y

-- The homotopy-colimit mapping frame is identified with diagram mapping
-- simplices, explicitly lifting the two possibly different Hom universes.
example : ColimitMapComparison.frameHom K I J fib ⋙
    (Functor.whiskeringRight C SSet.{v} SSet.{max w v}).obj SSet.uliftFunctor.{max w v,v} ≅
      ColimitMapComparison.diagramHom K I J fib ⋙
        (Functor.whiskeringRight C SSet.{max w v} SSet.{max w v}).obj
          SSet.uliftFunctor.{v,max w v} := ColimitMapComparison.liftedHomIso K I J fib

example [ModelCategory SSet.{v}]
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    (F : (K ⥤ C)ᵒᵖ) (Y : C) :
    weakEquivalences SSet.{v} (((ColimitMapComparison.left K I J cof fib).app F).app Y) ∧
      weakEquivalences SSet.{v} (((ColimitMapComparison.right K I J cof fib).app F).app Y) :=
  ⟨ColimitMapComparison.left_weakEquivalence K I J cof fib hcof F Y,
    ColimitMapComparison.right_weakEquivalence K I J cof fib hcof F Y⟩

example [ModelCategory SSet.{max w v}]
    (hcof : cofibrations SSet.{max w v} = MorphismProperty.monomorphisms _)
    (F : (K ⥤ C)ᵒᵖ) (Y : C) :
    weakEquivalences SSet.{max w v}
      (((ColimitMapComparison.diagramSourceComparison K I J fib).app F).app Y) :=
  ColimitMapComparison.diagramSourceComparison_weakEquivalence K I J fib hcof F Y

-- Final combinatorial inputs construct the source choices; they are not
-- extra assumptions in this consumer.
example [ModelCategory SSet.{v}]
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _) :
    ∃ cof₀ : MorphismProperty.FunctorialFactorizationData
        (cofibrations C) (trivialFibrations C),
      ∃ fib₀ : MorphismProperty.FunctorialFactorizationData
          (trivialCofibrations C) (fibrations C),
        ∀ (F : (K ⥤ C)ᵒᵖ) (Y : C),
          weakEquivalences SSet.{v}
            (((ColimitMapComparison.left K I J cof₀ fib₀).app F).app Y) ∧
          weakEquivalences SSet.{v}
            (((ColimitMapComparison.right K I J cof₀ fib₀).app F).app Y) := by
  have := SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.hasFunctorialFactorization_cofibration_trivialFibration I J
  have := SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.hasFunctorialFactorization_trivialCofibration_fibration I J
  let cof₀ := MorphismProperty.functorialFactorizationData (cofibrations C) (trivialFibrations C)
  let fib₀ := MorphismProperty.functorialFactorizationData (trivialCofibrations C) (fibrations C)
  exact ⟨cof₀, fib₀, fun F Y =>
    ⟨ColimitMapComparison.left_weakEquivalence K I J cof₀ fib₀ hcof F Y,
      ColimitMapComparison.right_weakEquivalence K I J cof₀ fib₀ hcof F Y⟩⟩

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.LatchingPreservation,
    `SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.AdjunctionHom,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FramePreservation,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameOverFunctor,
    `SerrePositivity.HomotopicalAlgebra.Diagram.ColimitFrame,
    `SerrePositivity.HomotopicalAlgebra.Diagram.ColimitMapComparison]
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
  logInfo m!"Colimit frame comparison audit passed: {count} declarations in {seen.size} modules."
