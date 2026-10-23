import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarSmallFreeChainTransfer

universe v u
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.SimplicialModel
open FreeGeneratorCategories OrdinaryBarFreeResolutionSeed OrdinaryBarChoiceBoundaryGluing
open OrdinaryBarRetractSystem OrdinaryBarFreeChainTransfer
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) (n : ℕ)

section WholeParameters
variable {U V : SSet.{max u v}} (j : U ⟶ parameters P n)
example {X Y : degree (D C) (n + 1)} (q : Quiver.Path X Y)
    (t : ℕ → (U ⟶ RetractChainFamily.interval)) :
    (ofPath hcof hfib P n j q t).length = q.length := ofPath_length hcof hfib P n j q t
example (k : V ⟶ U) {X Y : degree (D C) (n + 1)} (q : Quiver.Path X Y)
    (t : ℕ → (U ⟶ RetractChainFamily.interval)) :
    family hcof hfib P n (k ≫ j) q (fun r => k ≫ t r) =
      ParameterComposition.substitute k (family hcof hfib P n j q t) :=
  family_substitute hcof hfib P n j k q t
example (i : Fin (n + 2)) {X Y : degree (D C) (n + 2)} (q : Quiver.Path X Y)
    (t : ℕ → (U ⟶ RetractChainFamily.interval)) :
    family hcof hfib P n j
      ((FreeGeneratorFaces.fixedFace (D C) (n + 1) i).toPrefunctor.mapPath q) t =
      family hcof hfib P (n + 1) (j ≫ P ◁ SSet.stdSimplex.δ i) q t :=
  family_face hcof hfib P n j i q t
example (i : Fin (n + 1)) (k : U ⟶ parameters P (n + 1))
    {X Y : degree (D C) (n + 1)} (q : Quiver.Path X Y)
    (t : ℕ → (U ⟶ RetractChainFamily.interval)) :
    family hcof hfib P (n + 1) k ((degeneracyFunctor (D C) n i).toPrefunctor.mapPath q) t =
      family hcof hfib P n (k ≫ P ◁ OrdinaryBarFreeResolutionDegeneracyValues.sigma n i) q t :=
  family_degeneracy hcof hfib P n i k q t
example {X Y : degree (D C) (n + 1)} (q : Quiver.Path X Y) :
    family hcof hfib P n j q (fun _ => RetractChainFamily.zero U) =
      OrdinaryBarFreeTransferredFamilies.ofFamily hcof hfib (ParameterComposition.substitute j
        (OrdinaryBarFreeAmbientFamilies.family hcof hfib P n
          ((pathComposition (degree (D C) (n + 1))).map q))) := family_zero hcof hfib P n j q

-- Both local junction laws retain arbitrary whole prefix and suffix chains.
example {a d : D C} {X Y Z : degree (D C) (n + 1)}
    (q : chain hcof hfib U a X) (f : X ⟶ Y) (g : Y ⟶ Z)
    (t : U ⟶ RetractChainFamily.interval) (r : chain hcof hfib U Z d) :
    OrdinaryBarChainFamily.family hcof hfib
      ((snoc hcof hfib P n j (snoc hcof hfib P n j q f (RetractChainFamily.zero U)) g t).append r) =
      OrdinaryBarChainFamily.family hcof hfib ((snoc hcof hfib P n j q (f ≫ g) t).append r) :=
  zero_face hcof hfib P n j q f g t r
example {a d : D C} {X Y : degree (D C) (n + 1)}
    (q : chain hcof hfib U a X) (f : X ⟶ Y) (r : chain hcof hfib U Y d) :
    OrdinaryBarChainFamily.family hcof hfib
      ((snoc hcof hfib P n j q f (RetractChainFamily.one U)).append r) =
      ParameterComposition.comp
        (OrdinaryBarChainFamily.family hcof hfib
          (snoc hcof hfib P n j q f (RetractChainFamily.zero U)))
        (OrdinaryBarChainFamily.family hcof hfib r) := one_face hcof hfib P n j q f r
end WholeParameters

section SmallParameters
variable {T U : SSet.{v}} (j : UniverseLift.obj.{max u v} T ⟶ parameters P n)
example {X Y : degree (D C) (n + 1)} (q : Quiver.Path X Y)
    (t : ℕ → (UniverseLift.obj.{max u v} T ⟶ RetractChainFamily.interval)) :
    small hcof hfib X ⊗ T ⟶ small hcof hfib Y :=
  OrdinaryBarSmallFreeChainTransfer.family hcof hfib P n j q t
example (k : U ⟶ T) {X Y : degree (D C) (n + 1)} (q : Quiver.Path X Y)
    (t : ℕ → (UniverseLift.obj.{max u v} T ⟶ RetractChainFamily.interval)) :
    OrdinaryBarSmallFreeChainTransfer.family hcof hfib P n (UniverseLift.map k ≫ j) q
        (fun r => UniverseLift.map k ≫ t r) =
      ParameterComposition.substitute k
        (OrdinaryBarSmallFreeChainTransfer.family hcof hfib P n j q t) :=
  OrdinaryBarSmallFreeChainTransfer.family_substitute hcof hfib P n j k q t
example (i : Fin (n + 2)) {X Y : degree (D C) (n + 2)} (q : Quiver.Path X Y)
    (t : ℕ → (UniverseLift.obj.{max u v} T ⟶ RetractChainFamily.interval)) :
    OrdinaryBarSmallFreeChainTransfer.family hcof hfib P n j
      ((FreeGeneratorFaces.fixedFace (D C) (n + 1) i).toPrefunctor.mapPath q) t =
    OrdinaryBarSmallFreeChainTransfer.family hcof hfib P (n + 1)
      (j ≫ P ◁ SSet.stdSimplex.δ i) q t :=
  OrdinaryBarSmallFreeChainTransfer.family_face hcof hfib P n j i q t
end SmallParameters

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let modulePrefix := `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex
  let expected := #[Name.str modulePrefix "OrdinaryBarFreeChainTransfer",
    Name.str modulePrefix "OrdinaryBarSmallFreeChainTransfer"]
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
    throwError "Missing actual free chain transfer modules"
  logInfo m!"Free chain transfer audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
