import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open CoherentLiftRelative

section ArbitraryCategory
variable {D : Type u} [Category.{v} D] (F : ℕ ⥤ D) (P : D)
  (step : ∀ n (a : F.obj n ⟶ P),
    {b : F.obj (n + 1) ⟶ P // F.map (homOfLE (Nat.le_succ n)) ≫ b = a})
  (a₀ : F.obj 0 ⟶ P) (c : Cocone F) (hc : IsColimit c)

-- No model structure or equality of object and Hom universes is required here.
example {n m : ℕ} (f : n ⟶ m) :
    F.map f ≫ SerrePositivity.SequentialExtension.stage F P step a₀ m =
      SerrePositivity.SequentialExtension.stage F P step a₀ n :=
  SerrePositivity.SequentialExtension.stage_map F P step a₀ f

example (n : ℕ) :
    c.ι.app n ≫ SerrePositivity.SequentialExtension.descend F P step a₀ c hc =
      SerrePositivity.SequentialExtension.stage F P step a₀ n :=
  SerrePositivity.SequentialExtension.descend_stage F P step a₀ c hc n
end ArbitraryCategory

section ArbitrarySource
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (X Y : ResolutionObject C) (f : X.base ⟶ Y.base)
  {A K : SSet.{v}} (j : A ⟶ K) [Mono j] (a : A ⟶ CoherentLiftRelative.obj X Y f)

local notation "i₀" => vertexInclusion X Y f
local notation "b₀" => vertexData X Y f
local notation "p₀" => ResolutionLiftSpace.projection X Y f
local notation "hp₀" => ResolutionLiftSpace.projection_trivialFibration hcof X Y f
local notation "e" => RecursiveChoiceExtension.extend hcof hfib i₀ b₀ p₀ hp₀ j a

-- Every previously prescribed simplex, of any dimension, is kept literally.
example {n : ℕ} (s : SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ A) :
    (s ≫ j) ≫ e = s ≫ a :=
  RecursiveChoiceExtension.extend_prescribed hcof hfib i₀ b₀ p₀ hp₀ j a s

-- Each simplex of the global map uses the corresponding finite-stage choice.
example {n : ℕ} (s : SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ K) :
    s ≫ e = RecursiveChoiceExtension.simplexAtStage j s ≫
      RecursiveChoiceExtension.stage hcof hfib i₀ b₀ p₀ hp₀ j a (n + 1) :=
  RecursiveChoiceExtension.extend_simplex hcof hfib i₀ b₀ p₀ hp₀ j a s

example : i₀ ▷ K ≫ RelativeChoiceSpace.family i₀ b₀ e =
    vertices X Y f ◁ (SSet.stdSimplex.isTerminalObj₀.from K ≫
      RelativeChoiceSpace.pointUnitIso.hom) ≫ (ρ_ _).hom ≫ b₀ :=
  RecursiveChoiceExtension.fixed_boundary hcof hfib i₀ b₀ p₀ hp₀ j a

-- Its actual Kan action restricts to the original whole partial family.
example (Z : C) (t : CoherentLiftTuples.obj X Y f ⊗ K ⟶
    (cosimplicialHom Y.resolution.obj).obj Z) :
    CoherentLiftTuples.obj X Y f ◁ j ≫
      KanLiftAction.parameterized hcof hfib X Y f Z (RelativeChoiceSpace.family i₀ b₀ e) t =
    KanLiftAction.parameterized hcof hfib X Y f Z (RelativeChoiceSpace.family i₀ b₀ a)
      ((CoherentLiftTuples.obj X Y f ◁ j) ≫ t) := by
  rw [KanLiftAction.parameterized_naturality,
    RecursiveChoiceExtension.family_prescribed]

end ArbitrarySource

section RetainSelectedTriangle
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) (post : Bool)

-- A previously selected unit triangle remains the prescribed face of a tetrahedron.
example : SSet.stdSimplex.δ (0 : Fin 4) ≫
    RecursiveChoiceExtension.extend hcof hfib (vertexInclusion X Y f) (vertexData X Y f)
      (ResolutionLiftSpace.projection X Y f)
      (ResolutionLiftSpace.projection_trivialFibration hcof X Y f)
      (SSet.stdSimplex.δ (0 : Fin 4)) (CoherentLiftUnitComparison.triangle hcof hfib X Y f post) =
      CoherentLiftUnitComparison.triangle hcof hfib X Y f post :=
  RecursiveChoiceExtension.extend_initial hcof hfib _ _ _ _ _ _
end RetainSelectedTriangle

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.CategoryTheory.Limits.SequentialExtension,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RecursiveChoiceExtension]
  let mut count : Nat := 0
  let mut modules : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless modules.contains mod do modules := modules.push mod
  unless modules.size == expected.size do
    throwError "Some recursive extension modules were not audited"
  logInfo m!"Recursive choice extension audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
