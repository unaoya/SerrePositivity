import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe w v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open CoherentLiftRelative

section LargeParameters
variable {P : SSet.{v}} (hp : UniverseLift.BoundaryFillers P)
  {A K : SSet.{max w v}} (j : A ⟶ K) [Mono j] (a : A ⟶ UniverseLift.obj.{w} P)

-- Finite fillers lift between independent universes, with no larger model structure.
example : UniverseLift.BoundaryFillers (UniverseLift.obj.{w} P) :=
  UniverseLift.boundaryFillers hp

example : j ≫ LargeParameterExtension.extend hp j a = a :=
  LargeParameterExtension.extend_initial hp j a

-- Prescribed data of any dimension and size are retained.
example {L : SSet.{max w v}} (s : L ⟶ A) :
    (s ≫ j) ≫ LargeParameterExtension.extend hp j a = s ≫ a :=
  LargeParameterExtension.extend_prescribed hp j a s
end LargeParameters

section ArbitrarySource
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {X Y V : ResolutionObject C} (f : X.base ⟶ Y.base) (g : Y ⟶ V)

-- Only the small SSet model is supplied; object and Hom universes are independent.
example : nerve (ArrowFactorization g) ⟶
    UniverseLift.obj.{u} (AllFactorizationComparison.choiceSpace f g) :=
  AllFactorizationComparison.comparison hcof hfib f g

-- All existing factorization middle points are preserved exactly after the explicit lift.
example (a : ArrowFactorization g) :
    SSet.yonedaEquiv.symm (ComposableArrows.mk₀ a) ≫
      AllFactorizationComparison.comparison hcof hfib f g =
        (UniverseLift.stdIso.{u, v} 0).inv ≫ UniverseLift.map
          (CoherentLiftPostComposition.middlePoint hcof X Y a.middle V f a.left a.right ≫
            PostCompositionChain.choiceCast f a.fac) :=
  AllFactorizationComparison.comparison_point hcof hfib f g a

-- Each finite simplex still takes values in the original small comparison space.
example {n : ℕ} (c : AnchoredChain g n) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ postChoiceSpace X Y V f g :=
  AllFactorizationComparison.simplex hcof hfib f g c

example {n m : ℕ} (c : AnchoredChain g n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    SSet.stdSimplex.map θ ≫ AllFactorizationComparison.simplex hcof hfib f g c =
      AllFactorizationComparison.simplex hcof hfib f g (c.reindex θ.toOrderHom) :=
  AllFactorizationComparison.simplex_naturality hcof hfib f g c θ

example {n : ℕ} (c : AnchoredChain g n) :
    vertexInclusion X Y f ▷ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ≫
      RelativeChoiceSpace.family (vertexInclusion X Y f) (postBoundary X Y V f g)
        (AllFactorizationComparison.simplex hcof hfib f g c) =
      vertices X Y f ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫
        RelativeChoiceSpace.pointUnitIso.hom) ≫ (ρ_ _).hom ≫ postBoundary X Y V f g :=
  AllFactorizationComparison.simplex_fixed_boundary hcof hfib f g c

-- One global choice acts for every target and Hom parameter, without fibrancy of Z.
example {n m : ℕ} (c : AnchoredChain g n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (Z : C)
    (t : CoherentLiftTuples.obj X Y f ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶
      (cosimplicialHom V.resolution.obj).obj Z) :
    CoherentLiftTuples.obj X Y f ◁ SSet.stdSimplex.map θ ≫
      KanLiftAction.parameterized hcof hfib X V (f ≫ g.base) Z
        (RelativeChoiceSpace.family (vertexInclusion X Y f) (postBoundary X Y V f g)
          (AllFactorizationComparison.simplex hcof hfib f g c)) t =
      KanLiftAction.parameterized hcof hfib X V (f ≫ g.base) Z
        (RelativeChoiceSpace.family (vertexInclusion X Y f) (postBoundary X Y V f g)
          (AllFactorizationComparison.simplex hcof hfib f g (c.reindex θ.toOrderHom)))
        ((CoherentLiftTuples.obj X Y f ◁ SSet.stdSimplex.map θ) ≫ t) :=
  AllFactorizationComparison.action_naturality hcof hfib f g c θ Z t
end ArbitrarySource

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.CategoryTheory.NerveVertices,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftFillers,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.LargeParameterExtension,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationComparison]
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
    throwError "Some all-factorization modules were not audited"
  logInfo m!"All-factorization comparison audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
