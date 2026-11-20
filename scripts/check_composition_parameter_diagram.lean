import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarCompositionParameterDiagram
import Lean.Util.CollectAxioms

universe u v
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity SerrePositivity.SimplicialModel

-- The parameter category may be large; values are the original SSet universe.
example {T K : SSet.{v}} {f g z : T ⟶ K}
    (F : SSet.Homotopy f z) (G : SSet.Homotopy g z) : (Over T)ᵒᵖ ⥤ SSet.{v} :=
  ComparisonTriangleParameterDiagram.diagram F G
example {T K : SSet.{v}} {f g z : T ⟶ K}
    (F : SSet.Homotopy f z) (G : SSet.Homotopy g z) (a : KanComparisonTriangle.Data F G) :
    ComparisonTriangleParameterDiagram.point F G a ≫
      ComparisonTriangleParameterDiagram.projection F G = 𝟙 _ :=
  ComparisonTriangleParameterDiagram.point_projection F G a

open HomotopyFunctionComplex OrdinaryBarFreeResolutionSeed OrdinaryBarRetractSystem
open OrdinaryBarRelativeHomDescent
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) {T : SSet.{v}} {X Y Z : D C}
  (j : UniverseLift.obj.{max u v} T ⟶ P)
  (f : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
  (g : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C Y Z)
  (c : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P X Y)
  (d : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P Y Z)
  (e : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P X Z)

example : (Over T)ᵒᵖ ⥤ SSet.{v} := compositionParameterDiagram hcof hfib P j f g c d e
example {σ τ : (Over T)ᵒᵖ} (φ : σ ⟶ τ) :
    (compositionParameterPoint hcof hfib P j f g c d e).app σ ≫
      (compositionParameterDiagram hcof hfib P j f g c d e).map φ =
        (compositionParameterPoint hcof hfib P j f g c d e).app τ :=
  compositionParameterPoint_naturality hcof hfib P j f g c d e φ
example (σ : (Over T)ᵒᵖ) : (compositionParameterDiagram hcof hfib P j f g c d e).obj σ ≅
    compositionChoices hcof hfib P (UniverseLift.map σ.unop.hom ≫ j)
      (UniverseLift.map σ.unop.hom ≫ f) (UniverseLift.map σ.unop.hom ≫ g)
      (UniverseLift.map σ.unop.hom ≫ c) (UniverseLift.map σ.unop.hom ≫ d)
      (UniverseLift.map σ.unop.hom ≫ e) :=
  compositionParameterObjectIso hcof hfib P j f g c d e σ
example {U V : SSet.{v}} (i : U ⟶ V) [Mono i]
    (q : U ⟶ compositionChoices hcof hfib P j f g c d e) :
    ∃ r : V ⟶ compositionChoices hcof hfib P j f g c d e, i ≫ r = q ∧
      (Functor.const (Over T)ᵒᵖ).map i ≫ compositionParameterFamily hcof hfib P j f g c d e r =
        compositionParameterFamily hcof hfib P j f g c d e q :=
  compositionParameterFamily_extension hcof hfib P j f g c d e i q
example (a b : compositionTriangleData hcof hfib P j f g c d e) :
    (Functor.const (Over T)ᵒᵖ).map (SSet.stdSimplex.δ (1 : Fin 2)) ≫
      compositionParameterPointInterval hcof hfib P j f g c d e a b =
        compositionParameterPointOf hcof hfib P j f g c d e a :=
  compositionParameterPointInterval_zero hcof hfib P j f g c d e a b

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.ParameterChoiceDiagram,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.ComparisonTriangleParameterDiagram,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarCompositionParameterDiagram]
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
  unless modules.size == expected.size do throwError "Missing strict parameter diagram modules"
  logInfo m!"Strict parameter diagram audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
