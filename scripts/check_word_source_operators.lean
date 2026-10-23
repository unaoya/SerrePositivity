import SerrePositivity.CategoryTheory.Presentation.RetractWordPullback
import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarWordActionOperators

universe u v u' v' w w' uD vD
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity SerrePositivity.SimplicialModel

section General
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (F : C ⥤ D)
example (X Y : C) : SSet.uliftFunctor.{max u' v', max u v w}.obj
    (WordPresentationDiagram.smallHom.{u, v, w} C X Y) ⟶
    SSet.uliftFunctor.{max u v, max u' v' w}.obj
      (WordPresentationDiagram.smallHom.{u', v', w} D (F.obj X) (F.obj Y)) :=
  WordPresentationSourceMap.mapHom F X Y
variable {M : Type w} [MonoidWithZero M] {N : Type w'} [MonoidWithZero N]
  {E : Type uD} [Category.{vD} E] (R : RetractWords.Realization D M E) (h : N →*₀ M)
example : RetractWords.Realization C N E := R.pullback F h
example : RetractWords.map F h ⋙ R.functor = (R.pullback F h).functor := R.pullback_functor F h
end General

section CommonUniverse
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  (F : C ⥤ D) (G : D ⥤ E)
example (X Y : C) : WordPresentationSourceMap.mapHomSame.{u, v, w} (F ⋙ G) X Y =
    WordPresentationSourceMap.mapHomSame F X Y ≫
      WordPresentationSourceMap.mapHomSame G (F.obj X) (F.obj Y) :=
  WordPresentationSourceMap.mapHomSame_comp F G X Y
example (X Y : C) : WordPresentationSourceMap.mapHomSame.{u, v, w} (𝟭 C) X Y =
    𝟙 (WordPresentationDiagram.smallHom.{u, v, w} C X Y) :=
  WordPresentationSourceMap.mapHomSame_identity X Y
example (X : C) : WordPresentationDiagram.identity.{u, v, w} C X ≫
    WordPresentationSourceMap.mapHomSame F X X = WordPresentationDiagram.identity D (F.obj X) :=
  WordPresentationSourceMap.mapHomSame_unit F X
end CommonUniverse

section Actual
open HomotopyFunctionComplex OrdinaryBarWordAction OrdinaryBarWordActionOperators
open OrdinaryBarWordPresentation OrdinaryBarWordEvaluationOperators
open FreeGeneratorCategories OrdinaryBarFreeResolutionSeed OrdinaryBarChoiceBoundaryGluing
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) (n : ℕ)
example (i : Fin (n + 2)) (k : SimplexCategoryᵒᵖ) (t : (parameters P n).obj k) :
    RetractWords.map (FreeGeneratorFaces.fixedFace (D C) (n + 1) i)
        (MonoidWithZeroHom.id (WordSegment.degree.{max u v} k)) ⋙
      largeEvaluation (C := C) hcof hfib P n k t =
      largeEvaluation (C := C) hcof hfib P (n + 1) k ((P ◁ SSet.stdSimplex.δ i).app k t) :=
  evaluation_face hcof hfib P n i k t
example (i : Fin (n + 1)) (k : SimplexCategoryᵒᵖ) (t : (parameters P (n + 1)).obj k) :
    RetractWords.map (degeneracyFunctor (D C) n i)
        (MonoidWithZeroHom.id (WordSegment.degree.{max u v} k)) ⋙
      largeEvaluation (C := C) hcof hfib P (n + 1) k t =
      largeEvaluation (C := C) hcof hfib P n k
        ((P ◁ OrdinaryBarFreeResolutionDegeneracyValues.sigma n i).app k t) :=
  evaluation_degeneracy hcof hfib P n i k t
example {T : SSet.{v}} (i : Fin (n + 2))
    (j : UniverseLift.obj.{max u v} T ⟶ parameters P n)
    {X Y : degree (D C) (n + 2)}
    (f : UniverseLift.obj.{max u v} T ⟶ hom (C := C) (n + 1) X Y) :
    family hcof hfib P n j (f ≫ WordPresentationSourceMap.mapHomSame
        (FreeGeneratorFaces.fixedFace (D C) (n + 1) i) X Y) =
      family hcof hfib P (n + 1) (j ≫ P ◁ SSet.stdSimplex.δ i) f :=
  family_face hcof hfib P n i j f
example {T : SSet.{v}} (i : Fin (n + 1))
    (j : UniverseLift.obj.{max u v} T ⟶ parameters P (n + 1))
    {X Y : degree (D C) (n + 1)} (f : UniverseLift.obj.{max u v} T ⟶ hom (C := C) n X Y) :
    family hcof hfib P (n + 1) j (f ≫ WordPresentationSourceMap.mapHomSame
        (degeneracyFunctor (D C) n i) X Y) =
      family hcof hfib P n
        (j ≫ P ◁ OrdinaryBarFreeResolutionDegeneracyValues.sigma n i) f :=
  family_degeneracy hcof hfib P n i j f
end Actual

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[`SerrePositivity.CategoryTheory.Quiver.PathFunctorExt,
    `SerrePositivity.CategoryTheory.Presentation.RetractWordExt,
    `SerrePositivity.CategoryTheory.Presentation.RetractWordPullback,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.WordPresentationSourceMap,
    Name.str `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex
      "OrdinaryBarWordEvaluationOperators",
    Name.str `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex
      "OrdinaryBarWordActionOperators"]
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
  unless modules.size == expected.size do throwError "Missing word source operator modules"
  logInfo m!"Word source operator audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
