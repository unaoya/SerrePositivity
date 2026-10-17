import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open SSet.relativeCellComplexOfMono

section ModelIndependent
variable {A K Q : SSet.{v}} (j : A ⟶ K) [Mono j]

-- The zero-dimensional step requires no boundary data.
example (a : SkeletalCellGluing.stage j 0 ⟶ Q)
    (f : Cell j 0 → (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ Q)) (c : Cell j 0) :
    SkeletalCellGluing.cell j c ≫ SkeletalCellGluing.glue j a f
      (fun _ => SSet.boundary.hom_ext₀) = f c :=
  SkeletalCellGluing.glue_cell j a f _ c

-- In every dimension, compatibility of the attaching faces is an output.
example {n : ℕ} (a : SkeletalCellGluing.stage j (n + 2) ⟶ Q) (c : Cell j (n + 2)) :
    BoundaryGluing.StandardCompatible
      (fun k => SSet.boundary.ι k ≫ SkeletalCellGluing.boundary j c ≫ a) :=
  SkeletalCellGluing.attachingFaces_compatible j a c

-- Ordinary face equations suffice to assemble specified triangles.
example (a : SkeletalCellGluing.stage j 2 ⟶ Q)
    (triangles : Cell j 2 → (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ⟶ Q))
    (h : ∀ c (k : Fin 3), SSet.boundary.ι k ≫ SkeletalCellGluing.boundary j c ≫ a =
      SSet.stdSimplex.δ k ≫ triangles c) (c : Cell j 2) :
    SkeletalCellGluing.cell j c ≫ SkeletalCellGluing.glue j a triangles
      (SkeletalCellGluing.compatible_of_faces j a triangles h) = triangles c :=
  SkeletalCellGluing.glue_cell j a triangles _ c
end ModelIndependent

section ArbitrarySource
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (X Y : ResolutionObject C) (f : X.base ⟶ Y.base)
  {A K : SSet.{v}} (j : A ⟶ K) [Mono j]
  (a₀ : A ⟶ CoherentLiftRelative.obj X Y f)
  (prescribed : ∀ n, Cell j n → Option
    (SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ CoherentLiftRelative.obj X Y f))

local notation "i₀" => CoherentLiftRelative.vertexInclusion X Y f
local notation "b₀" => CoherentLiftRelative.vertexData X Y f
local notation "p₀" => ResolutionLiftSpace.projection X Y f
local notation "hp₀" => ResolutionLiftSpace.projection_trivialFibration hcof X Y f
local notation "e" => RelativeChoiceCells.assemble hcof hfib i₀ b₀ p₀ hp₀ j a₀ prescribed

-- The ordinary model axioms supply the whole system of actual cell fillers.
example : Nonempty (SkeletalCellGluing.Rule (Q := CoherentLiftRelative.obj X Y f) j) :=
  ⟨RelativeChoiceCells.rule hcof hfib i₀ b₀ p₀ hp₀ j⟩

example : j ≫ e = a₀ :=
  RelativeChoiceCells.assemble_initial hcof hfib i₀ b₀ p₀ hp₀ j a₀ prescribed

example : i₀ ▷ K ≫ RelativeChoiceSpace.family i₀ b₀ e =
    CoherentLiftRelative.vertices X Y f ◁ (SSet.stdSimplex.isTerminalObj₀.from K ≫
      RelativeChoiceSpace.pointUnitIso.hom) ≫ (ρ_ _).hom ≫ b₀ :=
  RelativeChoiceCells.fixed_boundary hcof hfib i₀ b₀ p₀ hp₀ j a₀ prescribed

-- The same global choice acts for every target and parameter; no fibrancy of Z is assumed.
example (Z : C) (t : CoherentLiftTuples.obj X Y f ⊗ K ⟶
    (cosimplicialHom Y.resolution.obj).obj Z) :
    CoherentLiftTuples.obj X Y f ◁ j ≫
      KanLiftAction.parameterized hcof hfib X Y f Z (RelativeChoiceSpace.family i₀ b₀ e) t =
    KanLiftAction.parameterized hcof hfib X Y f Z (RelativeChoiceSpace.family i₀ b₀ a₀)
      ((CoherentLiftTuples.obj X Y f ◁ j) ≫ t) := by
  rw [KanLiftAction.parameterized_naturality, RelativeChoiceCells.family_initial]

-- Retain an actual previously selected unit triangle. Only its three attaching
-- edge equations are required; the full boundary equation is proved below.
example (post : Bool) (c : Cell j 2) (q : (SSet.boundary.{v} 2).toSSet ⟶ A)
    (hq : q ≫ j = (SSet.boundary.{v} 2).ι ≫ c.map)
    (hs : prescribed 2 c = some (CoherentLiftUnitComparison.triangle hcof hfib X Y f post))
    (hfaces : ∀ k : Fin 3, SSet.boundary.ι k ≫ q ≫ a₀ =
      (CoherentLiftUnitComparison.data hcof hfib X Y f post).faces k) :
    c.map ≫ e = CoherentLiftUnitComparison.triangle hcof hfib X Y f post := by
  apply RelativeChoiceCells.assemble_prescribed hcof hfib i₀ b₀ p₀ hp₀ j a₀ prescribed
    c _ hs q hq
  apply SSet.boundary.hom_ext
  intro k
  simpa only [Category.assoc, SSet.boundary.ι_ι_assoc] using
    (hfaces k).trans (CoherentLiftUnitComparison.triangle_face hcof hfib X Y f post k).symm
end ArbitrarySource

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryGluing,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.SkeletalCellGluing,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RelativeChoiceCells]
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
  unless modules.size == expected.size do throwError "Some cell coherence modules were not audited"
  logInfo m!"Skeletal cell coherence audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
