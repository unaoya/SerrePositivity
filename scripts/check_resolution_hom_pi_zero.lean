import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.PiZero
import Lean.Util.CollectAxioms

noncomputable section
universe v u v' u'
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.Reedy
variable {C : Type u} [Category.{v} C] [ModelCategory C]

-- Arbitrary source, arbitrary ordinary resolution, and the actual localization.
-- There is no model structure on SSet or chosen source factorization assumption.
example (X Y : C) [IsFibrant Y] :
    SSet.π₀ ((cosimplicialHom (cosimplicialResolution X).obj).obj Y) ≃
      ((weakEquivalences C).Q.obj X ⟶ (weakEquivalences C).Q.obj Y) :=
  resolutionPiZeroLocalizationEquiv (weakEquivalences C).Q (cosimplicialResolution X) Y

example (X : C) :
    (cosimplicialCylinder (cosimplicialResolution X).obj
      (cosimplicialResolution X).homotopicallyConstant).IsGood :=
  cosimplicialCylinder_isGood _ (cosimplicialResolution X).cofibrant
    (cosimplicialResolution X).homotopicallyConstant

-- Independent object and morphism universes in the chosen ordinary localization.
example {H : Type u'} [Category.{v'} H] (L : C ⥤ H)
    [L.IsLocalization (weakEquivalences C)]
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    (X : Cᵒᵖ) (Y : C) :
    SSet.π₀ (((chosenResolutionHom cof fib).obj X).obj Y) ≃ (L.obj X.unop ⟶ L.obj Y) :=
  chosenResolutionHomPiZeroEquiv L cof fib X Y

-- Both-variable naturality is tested for arbitrary maps, not only weak equivalences.
example
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    {X X' : Cᵒᵖ} (f : X ⟶ X') {Y Y' : C} (g : Y ⟶ Y')
    (z : SSet.π₀ (((chosenResolutionHom cof fib).obj X).obj Y)) :
    chosenResolutionHomPiZeroEquiv (weakEquivalences C).Q cof fib X' Y'
      (SSet.mapπ₀ (((chosenResolutionHom cof fib).obj X').map g)
        (SSet.mapπ₀ (((chosenResolutionHom cof fib).map f).app Y) z)) =
      (weakEquivalences C).Q.map f.unop ≫
        chosenResolutionHomPiZeroEquiv (weakEquivalences C).Q cof fib X Y z ≫
          (weakEquivalences C).Q.map g :=
  (chosenResolutionHomPiZeroEquiv_naturality_target (weakEquivalences C).Q cof fib X' g _).trans
    ((congrArg (fun k ↦ k ≫ (weakEquivalences C).Q.map g)
      (chosenResolutionHomPiZeroEquiv_naturality_source
        (weakEquivalences C).Q cof fib f Y z)).trans (Category.assoc _ _ _))

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FiniteTensorBinaryCoproduct,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.BoundaryOne,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionCylinder,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.PiZero]
  let mut count : Nat := 0
  let mut seen : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless seen.contains mod do seen := seen.push mod
  for mod in expected do
    unless seen.contains mod do throwError "Module not audited: {mod}"
  logInfo m!"Resolution Hom pi-zero audit passed: {count} declarations in {seen.size} modules."
