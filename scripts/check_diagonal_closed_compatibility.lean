import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedCompatibility

universe w u v
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalClosed
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.SimplicialModel
open OrdinaryBarFreeResolutionSeed OrdinaryBarRetractSystem OrdinaryBarDiagonalClosedAction

section Generic
example {X Y Z T : SSet.{v}} (f : X ⊗ T ⟶ Y) (g : Y ⊗ T ⟶ Z) :
    curry (ParameterComposition.comp f g) =
      lift (curry f) (curry g) ≫ MonoidalClosed.comp X Y Z :=
  ClosedParameterComposition.curry_comp f g
example (X T : SSet.{v}) : curry (fst X T) = toUnit T ≫ MonoidalClosed.id X :=
  ClosedParameterComposition.curry_fst X T
end Generic

example {K P T : SSet.{v}} (f : K ⊗ T ⟶ P) :
    UniverseLift.map.{w} (curry f) ≫ (UniverseLiftParameterHom.closedIso K P).hom =
      curry (UniverseLift.tensorMap.{w} f) := UniverseLiftClosedCurry.curry_tensorMap f
example (K P Q : SSet.{v}) :
    ((UniverseLiftParameterHom.closedIso K P).hom ⊗ₘ
      (UniverseLiftParameterHom.closedIso P Q).hom) ≫
        MonoidalClosed.comp (UniverseLift.obj.{w} K) (UniverseLift.obj P) (UniverseLift.obj Q) =
    UniverseLiftClosedComposition.liftedComposition.{w} K P Q ≫
      (UniverseLiftParameterHom.closedIso K Q).hom :=
  UniverseLiftClosedComposition.composition K P Q
example (K : SSet.{v}) (T : SSet.{max w v}) :
    UniverseLiftClosedComposition.unitFrom K T =
      toUnit T ≫ MonoidalClosed.id (UniverseLift.obj.{w} K) ≫
        (UniverseLiftParameterHom.closedIso K K).inv :=
  UniverseLiftClosedComposition.unitFrom_eq K T

variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v})
example (X Y : D C) : P ⊗ OrdinaryBarFixedWordResolution.hom C X Y ⟶
    UniverseLift.obj.{max u v} ((ihom (small hcof hfib X)).obj (small hcof hfib Y)) :=
  mapping hcof hfib P X Y
example (X Y : D C) :
    uncurry (mapping hcof hfib P X Y ≫
      (UniverseLiftParameterHom.closedIso (small hcof hfib X) (small hcof hfib Y)).hom) =
      OrdinaryBarDiagonalAction.action hcof hfib P X Y := mapping_uncurry hcof hfib P X Y
example {T : SSet.{v}} {X Y : D C} (j : UniverseLift.obj.{max u v} T ⟶ P)
    (f : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y) :
    UniverseLift.lowerTensor (OrdinaryBarDiagonalAction.largeFamily hcof hfib P j f) =
      OrdinaryBarDiagonalEvaluation.family hcof hfib P j f :=
  OrdinaryBarDiagonalAction.lower_largeFamily hcof hfib P j f
example {T : SSet.{v}} {X Y Z : D C} (j : UniverseLift.obj.{max u v} T ⟶ P)
    (f : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
    (g : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C Y Z) :
    nativeFamily hcof hfib P j (lift f g ≫ OrdinaryBarFixedWordResolution.composition C X Y Z) =
      lift (nativeFamily hcof hfib P j f) (nativeFamily hcof hfib P j g) ≫
        MonoidalClosed.comp (small hcof hfib X) (small hcof hfib Y) (small hcof hfib Z) :=
  nativeFamily_comp hcof hfib P j f g
example {T : SSet.{v}} (X : D C) (j : UniverseLift.obj.{max u v} T ⟶ P) :
    nativeFamily hcof hfib P j
      (SSet.stdSimplex.isTerminalObj₀.from _ ≫ OrdinaryBarFixedWordResolution.identity C X) =
      toUnit T ≫ MonoidalClosed.id (small hcof hfib X) := nativeFamily_identity hcof hfib P X j
example {T U : SSet.{v}} {X Y : D C} (j : UniverseLift.obj.{max u v} T ⟶ P)
    (f : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y) (i : U ⟶ T) :
    nativeFamily hcof hfib P (UniverseLift.map i ≫ j) (UniverseLift.map i ≫ f) =
      i ≫ nativeFamily hcof hfib P j f := nativeFamily_substitute hcof hfib P j f i

example {T : SSet.{v}} {X Y : D C} (j : UniverseLift.obj.{max u v} T ⟶ P)
    (f : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y) :
    lift j f ≫ mapping hcof hfib P X Y =
      UniverseLift.map (nativeFamily hcof hfib P j f) :=
  OrdinaryBarDiagonalClosedCompatibility.mapping_nativeFamily hcof hfib P j f
example {T : SSet.{max u v}} {X Y Z : D C} (j : T ⟶ P)
    (f : T ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
    (g : T ⟶ OrdinaryBarFixedWordResolution.hom C Y Z) :
    lift j (lift f g ≫ OrdinaryBarFixedWordResolution.composition C X Y Z) ≫
        mapping hcof hfib P X Z =
      lift (lift j f ≫ mapping hcof hfib P X Y) (lift j g ≫ mapping hcof hfib P Y Z) ≫
        UniverseLiftClosedComposition.liftedComposition.{max u v}
          (small hcof hfib X) (small hcof hfib Y) (small hcof hfib Z) :=
  OrdinaryBarDiagonalClosedCompatibility.mapping_comp hcof hfib P j f g
example {T : SSet.{max u v}} (X : D C) (j : T ⟶ P) :
    lift j (SSet.stdSimplex.isTerminalObj₀.from T ≫
      OrdinaryBarFixedWordResolution.identity C X) ≫ mapping hcof hfib P X X =
        UniverseLiftClosedComposition.unitFrom (small hcof hfib X) T :=
  OrdinaryBarDiagonalClosedCompatibility.mapping_identity hcof hfib P X j

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[`SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftClosedCurry,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftClosedComposition,
    Name.str `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex
      "OrdinaryBarDiagonalClosedCompatibility",
    `SerrePositivity.HomotopicalAlgebra.Simplicial.ClosedParameterComposition,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalAction,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedAction]
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
  unless modules.size == expected.size do throwError "Missing diagonal closed action modules"
  logInfo m!"Diagonal closed compatibility audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
