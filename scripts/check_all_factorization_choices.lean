import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe w v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex

section LargeParameters
variable {P : SSet.{v}} (hp : UniverseLift.BoundaryFillers P)
  {A K : SSet.{max w v}} (j : A ⟶ K) [Mono j] (b : A ⟶ UniverseLift.obj.{w} P)

-- Neither a large model nor a fibrancy assumption appears in these inputs.
example {U V : SSet.{max w v}} (l : U ⟶ V) [Mono l]
    (a : U ⟶ RelativeChoiceSpace.obj j b) :
    ∃ e : V ⟶ RelativeChoiceSpace.obj j b, l ≫ e = a :=
  LargeParameterRelativeChoice.extension hp j b l a
example : UniverseLift.BoundaryFillers (RelativeChoiceSpace.obj j b) :=
  LargeParameterRelativeChoice.fillers hp j b

-- A whole family of choices is compared at once, rather than choosing intervals point by point.
example {T : SSet.{max w v}} (e₀ e₁ : T ⟶ RelativeChoiceSpace.obj j b) :
    SSet.Homotopy e₀ e₁ := LargeParameterRelativeChoice.parameterHomotopy hp j b e₀ e₁

example (e₀ e₁ : K ⟶ UniverseLift.obj.{w} P) (h₀ : j ≫ e₀ = b) (h₁ : j ≫ e₁ = b) :
    j ▷ SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk 1) ≫
        (LargeParameterRelativeChoice.homotopy hp j b e₀ e₁ h₀ h₁).h =
      A ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫ RelativeChoiceSpace.pointUnitIso.hom) ≫
        (ρ_ A).hom ≫ b :=
  LargeParameterRelativeChoice.homotopy_relative hp j b e₀ e₁ h₀ h₁
-- Moving boundary data are retained together with the old full parameterized family.
example {U V : SSet.{max w v}} (l : U ⟶ V) [Mono l]
    (a : K ⊗ U ⟶ UniverseLift.obj.{w} P) (c : A ⊗ V ⟶ UniverseLift.obj.{w} P)
    (hc : j ▷ U ≫ a = A ◁ l ≫ c) :
    ∃ e : K ⊗ V ⟶ UniverseLift.obj.{w} P, K ◁ l ≫ e = a ∧ j ▷ V ≫ e = c :=
  LargeParameterRelativeChoice.family_lifting hp j l a c hc
end LargeParameters

section ArbitraryModel
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {X Y V : ResolutionObject C} (f : X.base ⟶ Y.base) (g : Y ⟶ V)

-- The existing selected family is retained as a point of one space of all global systems.
example : SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 0) ⟶
    AllFactorizationChoices.obj hcof f g := AllFactorizationChoices.chosenPoint hcof hfib f g
example : SSet.Homotopy
    (AllFactorizationChoices.collapse hcof f g ≫ AllFactorizationChoices.chosenPoint hcof hfib f g)
    (𝟙 (AllFactorizationChoices.obj hcof f g)) := AllFactorizationChoices.contraction hcof hfib f g

-- Any already specified high-dimensional subfamily of systems can be retained.
example {A K : SSet.{max u v}} (j : A ⟶ K) [Mono j]
    (b : A ⟶ AllFactorizationChoices.obj hcof f g) :
    ∃ e : K ⟶ AllFactorizationChoices.obj hcof f g, j ≫ e = b :=
  AllFactorizationChoices.extension hcof hfib f g j b

example : nerve (ArrowFactorization g) ◁ SSet.ι₁ ≫
    AllFactorizationChoices.universalContraction hcof hfib f g =
      AllFactorizationChoices.universalFamily hcof f g :=
  AllFactorizationChoices.universalContraction_one hcof hfib f g

-- Move every prescribed factorization point, retaining the old systems as whole maps.
example {A K : SSet.{max u v}} (j : A ⟶ K) [Mono j]
    (a : nerve (ArrowFactorization g) ⊗ A ⟶
      UniverseLift.obj.{u} (AllFactorizationComparison.choiceSpace f g))
    (c : NerveVertices.vertices (ArrowFactorization g) ⊗ K ⟶
      UniverseLift.obj.{u} (AllFactorizationComparison.choiceSpace f g))
    (hc : NerveVertices.inclusion (ArrowFactorization g) ▷ A ≫ a =
      NerveVertices.vertices (ArrowFactorization g) ◁ j ≫ c) :
    ∃ e : nerve (ArrowFactorization g) ⊗ K ⟶
        UniverseLift.obj.{u} (AllFactorizationComparison.choiceSpace f g),
      nerve (ArrowFactorization g) ◁ j ≫ e = a ∧
        NerveVertices.inclusion (ArrowFactorization g) ▷ K ≫ e = c :=
  AllFactorizationChoices.extendMovingVertices hcof hfib f g j a c hc

variable (s : nerve (ArrowFactorization g) ⟶
    UniverseLift.obj.{u} (AllFactorizationComparison.choiceSpace f g))
  (hs : NerveVertices.inclusion (ArrowFactorization g) ≫ s =
    AllFactorizationComparison.vertexData hcof f g)

-- The comparison fixes all original factorization vertices throughout the interval.
example : NerveVertices.inclusion (ArrowFactorization g) ▷
    SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1) ≫
      (AllFactorizationChoices.homotopy hcof hfib f g s hs).h =
    NerveVertices.vertices (ArrowFactorization g) ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫
      RelativeChoiceSpace.pointUnitIso.hom) ≫ (ρ_ _).hom ≫
        AllFactorizationComparison.vertexData hcof f g :=
  AllFactorizationChoices.homotopy_fixed_vertices hcof hfib f g s hs

example {n : ℕ} (c : AnchoredChain g n)
    (t : (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1)).obj
      (Opposite.op (SimplexCategory.mk n))) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ AllFactorizationComparison.choiceSpace f g :=
  AllFactorizationChoices.simplex hcof hfib f g s hs c t
end ArbitraryModel

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.LargeParameterHomotopy,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.LargeParameterRelativeChoice,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.AllFactorizationChoices]
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
    throwError "Some relative global choice modules were not audited"
  logInfo m!"Relative global choice audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
