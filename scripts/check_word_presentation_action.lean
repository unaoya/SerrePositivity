import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarWordAction

universe u v w
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open SerrePositivity SerrePositivity.SimplicialModel

section Generic
open WordPresentationNaturality WordPresentationAction
variable {C : Type u} [Category.{w} C] {T : SSet.{v}}
  (F : C ⥤ ParameterCategory.Object T) (K : C → SSet.{v})
  (s : ∀ X, K X ⟶ (F.obj X).value) (p : ∀ X, (F.obj X).value ⟶ K X)
  (hs : ∀ X, s X ≫ p X = 𝟙 (K X))
  (H : ∀ X, SSet.Homotopy (𝟙 (F.obj X).value) (p X ≫ s X))
  (hP : ∀ X, (H X).h ≫ p X = fst (F.obj X).value WordSegment.interval ≫ p X)
  (hS : ∀ X, s X ▷ WordSegment.interval ≫ (H X).h = fst (K X) WordSegment.interval ≫ s X)
example {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (t : T.obj n) (X Y : C)
    (f : (WordPresentationDiagram.smallHom.{u, w, v} C X Y).obj n) (x : (K X).obj n) :
    (K Y).map θ ((R F K s p hs H hP hS n t).functor.map f x) =
      (R F K s p hs H hP hS m (T.map θ t)).functor.map
        ((WordPresentationDiagram.smallHom C X Y).map θ f) ((K X).map θ x) :=
  small_naturality F K s p hs H hP hS θ t X Y f x
example (X Y : C) : UniverseLift.obj.{max u w v} (K X) ⊗
    (UniverseLift.obj.{max u w v} T ⊗ WordPresentationDiagram.smallHom.{u, w, v} C X Y) ⟶
      UniverseLift.obj.{max u w v} (K Y) := action F K s p hs H hP hS X Y
example {U : SSet.{max u w v}} (X Y Z : C)
    (t : U ⟶ UniverseLift.obj.{max u w v} T)
    (f : U ⟶ WordPresentationDiagram.smallHom.{u, w, v} C X Y)
    (g : U ⟶ WordPresentationDiagram.smallHom.{u, w, v} C Y Z) :
    ParameterComposition.comp (family F K s p hs H hP hS X Y t f)
        (family F K s p hs H hP hS Y Z t g) =
      family F K s p hs H hP hS X Z t (lift f g ≫ WordPresentationDiagram.composition C X Y Z) :=
  family_comp F K s p hs H hP hS X Y Z t f g
end Generic

section Actual
open HomotopyFunctionComplex OrdinaryBarWordAction
open FreeGeneratorCategories OrdinaryBarFreeResolutionSeed OrdinaryBarChoiceBoundaryGluing
open OrdinaryBarRetractSystem
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) (n : ℕ) {T : SSet.{v}}
  (j : UniverseLift.obj.{max u v} T ⟶ parameters P n)
example {X Y : degree (D C) (n + 1)}
    (f : UniverseLift.obj.{max u v} T ⟶ hom (C := C) n X Y) :
    small hcof hfib X ⊗ T ⟶ small hcof hfib Y := family hcof hfib P n j f
example (X : degree (D C) (n + 1)) :
    family hcof hfib P n j
      (SSet.stdSimplex.isTerminalObj₀.from _ ≫ WordPresentationDiagram.identity _ X) =
      fst (small hcof hfib X) T := family_identity hcof hfib P n j X
example {X Y Z : degree (D C) (n + 1)}
    (f : UniverseLift.obj.{max u v} T ⟶ hom (C := C) n X Y)
    (g : UniverseLift.obj.{max u v} T ⟶ hom (C := C) n Y Z) :
    ParameterComposition.comp (family hcof hfib P n j f) (family hcof hfib P n j g) =
      family hcof hfib P n j (lift f g ≫ WordPresentationDiagram.composition _ X Y Z) :=
  family_comp hcof hfib P n j f g
example {U : SSet.{v}} (i : U ⟶ T) {X Y : degree (D C) (n + 1)}
    (f : UniverseLift.obj.{max u v} T ⟶ hom (C := C) n X Y) :
    family hcof hfib P n (UniverseLift.map i ≫ j) (UniverseLift.map i ≫ f) =
      ParameterComposition.substitute i (family hcof hfib P n j f) :=
  family_substitute hcof hfib P n j i f
end Actual

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[`SerrePositivity.CategoryTheory.Quiver.PathNatTrans,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.WordPresentationNaturality,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.WordPresentationAction,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarWordAction]
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
  unless modules.size == expected.size do throwError "Missing word presentation action modules"
  logInfo m!"Word presentation action audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
