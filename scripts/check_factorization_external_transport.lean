import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe w v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open CoherentLiftRelative

section GeneralCategory
variable {D : Type u} [Category.{v} D] {Y V Y' V' Y'' V'' : D}
  (g : Y ⟶ V) (a : Y' ⟶ Y) (b : V ⟶ V') (h : Y' ⟶ V') (e : (a ≫ g) ≫ b = h)
  (a' : Y'' ⟶ Y') (b' : V' ⟶ V'') (k : Y'' ⟶ V'') (e' : (a' ≫ h) ≫ b' = k)

-- Actual functors retain every middle object and middle map.
example : ArrowFactorization.transport g a b h e ⋙ ArrowFactorization.forget h =
    ArrowFactorization.forget g := ArrowFactorization.transport_forget g a b h e

example : AnchoredChain.transport g (𝟙 Y) (𝟙 V) g (by simp) = 𝟙 _ :=
  AnchoredChain.transport_id g

example : AnchoredChain.transport g a b h e ≫ AnchoredChain.transport h a' b' k e' =
    AnchoredChain.transport g (a' ≫ a) (b ≫ b') k
      (ArrowFactorization.context_comp g a b h e a' b' k e') :=
  AnchoredChain.transport_comp g a b h e a' b' k e'

example {n : ℕ} (c : AnchoredChain g n) :
    ((AnchoredChain.transport g a b h e).app (Opposite.op (SimplexCategory.mk n)) c).diagram =
      c.diagram := AnchoredChain.transport_diagram g a b h e c

example :
    AnchoredChain.mapFunctor (ArrowFactorization.preTo g a (a ≫ g) rfl) ≫
      AnchoredChain.mapFunctor (ArrowFactorization.postTo (a ≫ g) b h e) =
    AnchoredChain.mapFunctor (ArrowFactorization.postTo g b (g ≫ b) rfl) ≫
      AnchoredChain.mapFunctor
        (ArrowFactorization.preTo (g ≫ b) a h ((Category.assoc a g b).symm.trans e)) :=
  AnchoredChain.mapFunctor_pre_post g a b h e

-- The transport is a single simplicial map, natural under all ordinal operators.
example {i j : SimplexCategoryᵒᵖ} (θ : i ⟶ j) :
    (AnchoredChain.simplicial g).map θ ≫ (AnchoredChain.transport g a b h e).app j =
      (AnchoredChain.transport g a b h e).app i ≫ (AnchoredChain.simplicial h).map θ :=
  (AnchoredChain.transport g a b h e).naturality θ
end GeneralCategory

section LargeParameters
variable {P : SSet.{v}} (hp : UniverseLift.BoundaryFillers P) {K : SSet.{max w v}}
  (e₀ e₁ : K ⟶ UniverseLift.obj.{w} P)

-- Neither a model nor a fibrancy hypothesis is supplied in the larger universe.
example : SSet.Homotopy e₀ e₁ := LargeParameterHomotopy.homotopy hp e₀ e₁
example : SSet.ι₀ ≫ LargeParameterHomotopy.hom hp e₀ e₁ = e₀ :=
  LargeParameterHomotopy.at_zero hp e₀ e₁
example : SSet.ι₁ ≫ LargeParameterHomotopy.hom hp e₀ e₁ = e₁ :=
  LargeParameterHomotopy.at_one hp e₀ e₁
end LargeParameters

section ArbitraryModel
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {X Y V W : ResolutionObject C} (f : X.base ⟶ Y.base) (g : Y ⟶ V) (b : V ⟶ W)

example : AllFactorizationPost.direct hcof hfib f g b =
    AnchoredChain.mapFunctor (ArrowFactorization.postTo g b (g ≫ b) rfl) ≫
      AllFactorizationComparison.chainComparison hcof hfib f (g ≫ b) := rfl

example : AllFactorizationPost.transported hcof hfib f g b =
    AllFactorizationComparison.chainComparison hcof hfib f g ≫
      UniverseLift.map (CoherentLiftPostComposition.firstMap hcof X Y V W f g b) := rfl

-- One homotopy compares the two actual global families on all source chains.
example : SSet.Homotopy (AllFactorizationPost.direct hcof hfib f g b)
    (AllFactorizationPost.transported hcof hfib f g b) :=
  AllFactorizationPost.homotopy hcof hfib f g b

example : SSet.ι₀ ≫ (AllFactorizationPost.homotopy hcof hfib f g b).h =
    AllFactorizationPost.direct hcof hfib f g b :=
  (AllFactorizationPost.homotopy hcof hfib f g b).h₀

example : SSet.ι₁ ≫ (AllFactorizationPost.homotopy hcof hfib f g b).h =
    AllFactorizationPost.transported hcof hfib f g b :=
  (AllFactorizationPost.homotopy hcof hfib f g b).h₁

example {n : ℕ} (c : AnchoredChain g n)
    (t : (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1)).obj
      (Opposite.op (SimplexCategory.mk n))) :
    vertexInclusion X Y f ▷ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ≫
      RelativeChoiceSpace.family (vertexInclusion X Y f) (postBoundary X Y W f (g ≫ b))
        (AllFactorizationPost.simplex hcof hfib f g b c t) =
      vertices X Y f ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫
        RelativeChoiceSpace.pointUnitIso.hom) ≫ (ρ_ _).hom ≫ postBoundary X Y W f (g ≫ b) :=
  AllFactorizationPost.simplex_fixed_boundary hcof hfib f g b c t
end ArbitraryModel

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.CategoryTheory.ArrowFactorizationTransport,
    `SerrePositivity.CategoryTheory.AnchoredChainTransport,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.LargeParameterHomotopy,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPost]
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
    throwError "Some external transport modules were not audited"
  logInfo m!"Factorization external transport audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
