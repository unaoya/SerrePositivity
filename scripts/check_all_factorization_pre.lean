import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe w v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed HomotopicalAlgebra
open SerrePositivity SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open CoherentLiftRelative

section LargeParameters
variable {P : SSet.{v}} (hp : UniverseLift.BoundaryFillers P) (K : SSet.{max w v})

-- No model structure, fibrancy, or smallness of K is supplied.
example : UniverseLift.BoundaryFillers ((ihom K).obj (UniverseLift.obj.{w} P)) :=
  LargeParameterMapping.fillers hp K

-- Boundary maps are retained as actual maps on the entire parameter K.
example (d : ℕ)
    (b : (SSet.boundary.{max w v} d).toSSet ⟶ (ihom K).obj (UniverseLift.obj.{w} P)) :
    (K ◁ (SSet.boundary.{max w v} d).ι) ≫
      uncurry (LargeParameterMapping.fill hp K d b) = uncurry b := by
  rw [← uncurry_natural_left, LargeParameterMapping.fill_boundary]
example {n : ℕ}
    (f : Fin (n + 3) → (SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk (n + 1)) ⟶
      (ihom K).obj (UniverseLift.obj.{w} P))) (hf : BoundaryGluing.StandardCompatible f)
    (k : Fin (n + 3)) :
    K ◁ SSet.stdSimplex.δ k ≫ uncurry (LargeParameterMapping.fillFaces hp K f hf) =
      uncurry (f k) :=
  LargeParameterMapping.fillFaces_uncurry_face hp K f hf k
end LargeParameters

section ArbitraryModel
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {X' X Y V : ResolutionObject C} (a : X' ⟶ X) (f : X.base ⟶ Y.base) (g : Y ⟶ V)
  (φ : ResolutionLiftPrecomposition.FrameMap a)

-- The new family really uses the precomposed base arrow and strict tuple transport.
example : AllFactorizationPre.direct hcof hfib a f g φ =
    AllFactorizationComparison.chainComparison hcof hfib (a.base ≫ f) g ≫
      UniverseLift.map (CoherentLiftMixedComparison.mapBD hcof X' X Y V a f g φ) := rfl

-- The old family is acted on by the actual chosen frame map.
example : AllFactorizationPre.transported hcof hfib a f g φ =
    AllFactorizationComparison.chainComparison hcof hfib f g ≫
      UniverseLift.map (CoherentLiftMixedComparison.mapAC X' X Y V a f g φ) := rfl

example : SSet.Homotopy (AllFactorizationPre.direct hcof hfib a f g φ)
    (AllFactorizationPre.transported hcof hfib a f g φ) :=
  AllFactorizationPre.homotopy hcof hfib a f g φ

example : SSet.ι₀ ≫ (AllFactorizationPre.homotopy hcof hfib a f g φ).h =
    AllFactorizationPre.direct hcof hfib a f g φ :=
  (AllFactorizationPre.homotopy hcof hfib a f g φ).h₀

example : SSet.ι₁ ≫ (AllFactorizationPre.homotopy hcof hfib a f g φ).h =
    AllFactorizationPre.transported hcof hfib a f g φ :=
  (AllFactorizationPre.homotopy hcof hfib a f g φ).h₁

example {n : ℕ} (c : AnchoredChain g n)
    (t : (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1)).obj
      (Opposite.op (SimplexCategory.mk n))) :
    vertexInclusion X Y f ▷ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ≫
      RelativeChoiceSpace.family (vertexInclusion X Y f)
        (CoherentLiftMixedComparison.boundary X' X Y V a f g φ)
        (AllFactorizationPre.simplex hcof hfib a f g φ c t) =
      vertices X Y f ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫
        RelativeChoiceSpace.pointUnitIso.hom) ≫ (ρ_ _).hom ≫
          CoherentLiftMixedComparison.boundary X' X Y V a f g φ :=
  AllFactorizationPre.simplex_fixed_boundary hcof hfib a f g φ c t

-- Simultaneous naturality of the chain and interval parameters.
example {n m : ℕ} (c : AnchoredChain g n)
    (t : (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1)).obj
      (Opposite.op (SimplexCategory.mk n)))
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    SSet.stdSimplex.map θ ≫ AllFactorizationPre.simplex hcof hfib a f g φ c t =
      AllFactorizationPre.simplex hcof hfib a f g φ (c.reindex θ.toOrderHom)
        ((SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1)).map θ.op t) :=
  AllFactorizationPre.simplex_naturality hcof hfib a f g φ c t θ

-- Higher fillers are available over all chains at once, with values lifted from small Q.
example : UniverseLift.BoundaryFillers
    ((ihom (AnchoredChain.simplicial g)).obj
      (UniverseLift.obj.{u} (AllFactorizationPre.choiceSpace a f g φ))) :=
  LargeParameterMapping.fillers (AllFactorizationPre.fillers hcof hfib a f g φ) _
end ArbitraryModel

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.LargeParameterMapping,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPre]
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
    throwError "Some global precomposition modules were not audited"
  logInfo m!"Global precomposition audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
