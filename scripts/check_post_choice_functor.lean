import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe w v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex

section GeneralParameters
variable {P : SSet.{v}} (hp : UniverseLift.BoundaryFillers P) {K : SSet.{max w v}}
  {e₀ e₁ : K ⟶ UniverseLift.obj.{w} P} (H H' : SSet.Homotopy e₀ e₁)

-- The actual old and new homotopies survive as faces of a single comparison.
example : SSet.ι₀ ≫ (HomotopyEndpointComparison.homotopy hp H H').h = H.h :=
  (HomotopyEndpointComparison.homotopy hp H H').h₀
example : SSet.ι₁ ≫ (HomotopyEndpointComparison.homotopy hp H H').h = H'.h :=
  (HomotopyEndpointComparison.homotopy hp H H').h₁
example : (K ◁ (SSet.boundary.{max w v} 1).ι) ▷
    SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk 1) ≫
      (HomotopyEndpointComparison.homotopy hp H H').h =
      (K ⊗ (SSet.boundary.{max w v} 1).toSSet) ◁
          (SSet.stdSimplex.isTerminalObj₀.from _ ≫ RelativeChoiceSpace.pointUnitIso.hom) ≫
        (ρ_ _).hom ≫ LargeParameterHomotopy.boundaryMap e₀ e₁ :=
  HomotopyEndpointComparison.fixed_endpoints hp H H'
end GeneralParameters

section ArbitraryModel
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {X Y V W : ResolutionObject C} (f : X.base ⟶ Y.base) (g : Y ⟶ V) (b : V ⟶ W)

-- Equality of the original factorization points precedes any choice of a homotopy.
example (p : ArrowFactorization g) :
    AllFactorizationComparison.point hcof f (g ≫ b)
        ((ArrowFactorization.postTo g b (g ≫ b) rfl).obj p) =
      AllFactorizationComparison.point hcof f g p ≫
        CoherentLiftPostComposition.firstMap hcof X Y V W f g b :=
  AllFactorizationPostPoints.point_post hcof f g b p

example : AllFactorizationPostRelative.vertexInclusion g ▷
    SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1) ≫
      (AllFactorizationPostRelative.homotopy hcof hfib f g b).h =
      NerveVertices.vertices (ArrowFactorization g) ◁
          (SSet.stdSimplex.isTerminalObj₀.from _ ≫ RelativeChoiceSpace.pointUnitIso.hom) ≫
        (ρ_ _).hom ≫ AllFactorizationPostRelative.vertexBoundary hcof f g b :=
  AllFactorizationPostRelative.fixed_vertices hcof hfib f g b

example : SSet.ι₀ ≫ (AllFactorizationPostRelative.oldComparison hcof hfib f g b).h =
    (AllFactorizationPost.homotopy hcof hfib f g b).h :=
  (AllFactorizationPostRelative.oldComparison hcof hfib f g b).h₀
example : SSet.ι₁ ≫ (AllFactorizationPostRelative.oldComparison hcof hfib f g b).h =
    (AllFactorizationPostRelative.homotopy hcof hfib f g b).h :=
  (AllFactorizationPostRelative.oldComparison hcof hfib f g b).h₁

-- All contexts, not merely a selected finite list of arrows, form one small-valued functor.
example : Under Y ⥤ SSet.{v} := PostChoiceFunctor.functor hcof f
example (G H K : Under Y) (p : G ⟶ H) (q : H ⟶ K) :
    (PostChoiceFunctor.functor hcof f).map (p ≫ q) =
      (PostChoiceFunctor.functor hcof f).map p ≫ (PostChoiceFunctor.functor hcof f).map q :=
  (PostChoiceFunctor.functor hcof f).map_comp p q
example (G : Under Y) :
    trivialFibrations SSet.{v} ((PostChoiceFunctor.projection hcof f).app G) :=
  PostChoiceFunctor.projection_trivialFibration hcof f hfib G
example (G : Under Y) : weakEquivalences SSet.{v} ((PostChoiceFunctor.point hcof f).app G) :=
  PostChoiceFunctor.point_weakEquivalence hcof f hfib G

-- The section is natural in every under-category morphism.
example {G H : Under Y} (p : G ⟶ H) :
    (PostChoiceFunctor.point hcof f).app G ≫ (PostChoiceFunctor.functor hcof f).map p =
      (PostChoiceFunctor.point hcof f).app H := by
  have h := ((PostChoiceFunctor.point hcof f).naturality p).symm
  change _ = (𝟙 _) ≫ (PostChoiceFunctor.point hcof f).app H at h
  exact h.trans (Category.id_comp _)
end ArbitraryModel

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPostPoints,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPostRelative,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.HomotopyEndpointComparison,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.PostChoiceFunctor]
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
    throwError "Some strict postcomposition modules were not audited"
  logInfo m!"Strict postcomposition choice audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
