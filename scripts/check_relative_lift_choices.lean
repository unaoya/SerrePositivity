import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

-- The actual relative extension fiber is Kan and its actual projection is
-- a trivial fibration. All input data are ordinary simplicial sets and maps.
example {V T P : SSet.{v}} (i : V ⟶ T) [Mono i] (b : V ⟶ P)
    (p : P ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
    (hp : trivialFibrations SSet.{v} p) :
    trivialFibrations SSet.{v} (RelativeChoiceSpace.projection i b) ∧
      SSet.KanComplex (RelativeChoiceSpace.obj i b) :=
  ⟨RelativeChoiceSpace.projection_trivialFibration hcof hfib i b p hp,
    RelativeChoiceSpace.kanComplex hcof hfib i b p hp⟩

-- Extend a parameter family while fixing its original boundary throughout
-- the entire parameter, not just at the vertices.
example {V T P : SSet.{v}} (i : V ⟶ T) [Mono i] (b : V ⟶ P)
    (p : P ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
    (hp : trivialFibrations SSet.{v} p) {K L : SSet.{v}} (j : K ⟶ L) [Mono j]
    (a : K ⟶ RelativeChoiceSpace.obj i b) :
    ∃ e : L ⟶ RelativeChoiceSpace.obj i b, j ≫ e = a ∧
      i ▷ L ≫ RelativeChoiceSpace.family i b e =
        V ◁ (SSet.stdSimplex.isTerminalObj₀.from L ≫ RelativeChoiceSpace.pointUnitIso.hom) ≫
          (ρ_ V).hom ≫ b := by
  obtain ⟨e, he⟩ := RelativeChoiceSpace.extension hcof hfib i b p hp j a
  exact ⟨e, he, RelativeChoiceSpace.family_fixed_boundary i b e⟩

section ArbitrarySource
variable {C : Type u} [Category.{v} C] [ModelCategory C]

-- A relative homotopy between the two whole postcomposition families acts
-- into the existing Kan target. Check both exact endpoints and its fixed
-- strict-lift vertices, simultaneously for every target and Hom parameter.
example (X Y W : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W) :
    ∃ H : CoherentLiftTuples.obj X Y f ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶
        ResolutionLiftSpace.obj X W (f ≫ g.base),
      ∀ (Z : C) (t : CoherentLiftTuples.obj X Y f ⊗
          SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶
            (cosimplicialHom W.resolution.obj).obj Z),
        CoherentLiftTuples.obj X Y f ◁ SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫
            KanLiftAction.parameterized hcof hfib X W (f ≫ g.base) Z H t =
          KanLiftAction.parameterized hcof hfib X W (f ≫ g.base) Z
            (CoherentLiftTuples.obj X Y f ◁ RelativeChoiceSpace.pointUnitIso.hom ≫
              (ρ_ _).hom ≫ CoherentLiftRelative.postLeft hcof X Y W f g)
            ((CoherentLiftTuples.obj X Y f ◁
              SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2))) ≫ t) ∧
        CoherentLiftTuples.obj X Y f ◁ SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) ≫
            KanLiftAction.parameterized hcof hfib X W (f ≫ g.base) Z H t =
          KanLiftAction.parameterized hcof hfib X W (f ≫ g.base) Z
            (CoherentLiftTuples.obj X Y f ◁ RelativeChoiceSpace.pointUnitIso.hom ≫
              (ρ_ _).hom ≫ CoherentLiftRelative.postRight hcof X Y W f g)
            ((CoherentLiftTuples.obj X Y f ◁
              SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2))) ≫ t) ∧
        CoherentLiftRelative.vertexInclusion X Y f ▷
            SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ≫
              KanLiftAction.parameterized hcof hfib X W (f ≫ g.base) Z H t =
          KanLiftAction.parameterized hcof hfib X W (f ≫ g.base) Z
            (CoherentLiftRelative.vertices X Y f ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫
              RelativeChoiceSpace.pointUnitIso.hom) ≫ (ρ_ _).hom ≫
                CoherentLiftRelative.postBoundary X Y W f g)
            ((CoherentLiftRelative.vertexInclusion X Y f ▷
              SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1)) ≫ t) := by
  obtain ⟨H, h₀, h₁, hb⟩ := CoherentLiftRelative.post_relative_homotopy hcof hfib X Y W f g
  refine ⟨H, fun Z t => ⟨?_, ?_, ?_⟩⟩
  · rw [KanLiftAction.parameterized_naturality, h₀]
  · rw [KanLiftAction.parameterized_naturality, h₁]
  · rw [KanLiftAction.parameterized_naturality, hb]

-- Higher relative comparisons extend with all already specified boundary data.
example (X Y W : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W) (n : ℕ)
    (a : (SSet.boundary.{v} n).toSSet ⟶ CoherentLiftRelative.postChoiceSpace X Y W f g) :
    ∃ e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶
        CoherentLiftRelative.postChoiceSpace X Y W f g, (SSet.boundary.{v} n).ι ≫ e = a :=
  CoherentLiftRelative.postChoiceSpace_extension hcof hfib X Y W f g _ a

-- Source precomposition has the same fixed-vertex comparison for every
-- actual outer frame map, without a functorial source choice assumption.
example (X Y W : ResolutionObject C) (f : X ⟶ Y) (g : Y.base ⟶ W.base)
    (φ : ResolutionLiftPrecomposition.FrameMap f) :
    Nonempty (RelativeChoiceSpace.FixedBoundaryHomotopy
      (CoherentLiftRelative.vertexInclusion Y W g) (CoherentLiftRelative.preBoundary X Y W f g)
      (CoherentLiftRelative.preLeft hcof X Y W f g φ)
      (CoherentLiftRelative.preRight hcof X Y W f g)) :=
  CoherentLiftRelative.pre_relative_homotopy hcof hfib X Y W f g φ

example (X Y W : ResolutionObject C) (f : X ⟶ Y) (g : Y.base ⟶ W.base) (n : ℕ)
    (a : (SSet.boundary.{v} n).toSSet ⟶ CoherentLiftRelative.preChoiceSpace X Y W f g) :
    ∃ e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶
        CoherentLiftRelative.preChoiceSpace X Y W f g, (SSet.boundary.{v} n).ι ≫ e = a :=
  CoherentLiftRelative.preChoiceSpace_extension hcof hfib X Y W f g _ a

end ArbitrarySource

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.FixedBoundaryExtensions,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.VertexTuples,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.CoherentLiftRelative]
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
  unless modules.size == expected.size do throwError "Some relative choice modules were not audited"
  logInfo m!"Relative lift choice audit passed: {count} declarations in {modules.size} modules, \
    standard axioms only."
