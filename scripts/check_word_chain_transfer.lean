import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarSmallFreeWordChainTransfer

universe v u
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.SimplicialModel
open FreeGeneratorCategories OrdinaryBarFreeResolutionSeed OrdinaryBarChoiceBoundaryGluing
open OrdinaryBarRetractSystem OrdinaryBarFreeWordChainTransfer
section Generic
open WordRetractChainFamily
variable {ι : Type u} (E K : ι → SSet.{v}) (s : ∀ i, K i ⟶ E i) (p : ∀ i, E i ⟶ K i)
  (hs : ∀ i, s i ≫ p i = 𝟙 (K i))
  (H : ∀ i, SSet.Homotopy (𝟙 (E i)) (p i ≫ s i))
  (hP : ∀ i, (H i).h ≫ p i = fst (E i) WordSegment.interval ≫ p i)
  (hS : ∀ i, s i ▷ WordSegment.interval ≫ (H i).h =
    fst (K i) WordSegment.interval ≫ s i)
example {T : SSet.{v}} {a b c d : ι} (q : Chain E T a b)
    (f : E b ⊗ T ⟶ E c) (t w : T ⟶ WordSegment.obj) (r : Chain E T c d) :
    transfer E K s p hs H hP hS
      (((q.familySnoc f t).familySnoc (ParameterComposition.const T (𝟙 (E c))) w).append r) =
      transfer E K s p hs H hP hS
        ((q.familySnoc f (lift t w ≫ WordSegment.mul)).append r) :=
  WordRetractChainFamily.interior_identity E K s p hs H hP hS q f t w r
example {T : SSet.{v}} {a b : ι} (q : RetractChainFamily.Chain E T a b) :
    transfer E K s p hs H hP hS (Chain.ofInterval q) =
      RetractChainFamily.transfer E K s p H q := transfer_ofInterval E K s p hs H hP hS q
end Generic

variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) (n : ℕ)

section WholeParameters
variable {U V : SSet.{max u v}} (j : U ⟶ parameters P n)
example {X Y : degree (D C) (n + 1)} (q : Quiver.Path X Y)
    (t : ℕ → (U ⟶ WordSegment.obj)) :
    (ofPath hcof hfib P n j q t).length = q.length := ofPath_length hcof hfib P n j q t
example (k : V ⟶ U) {X Y : degree (D C) (n + 1)} (q : Quiver.Path X Y)
    (t : ℕ → (U ⟶ WordSegment.obj)) :
    family hcof hfib P n (k ≫ j) q (fun r => k ≫ t r) =
      ParameterComposition.substitute k (family hcof hfib P n j q t) :=
  family_substitute hcof hfib P n j k q t
example (i : Fin (n + 2)) {X Y : degree (D C) (n + 2)} (q : Quiver.Path X Y)
    (t : ℕ → (U ⟶ WordSegment.obj)) :
    family hcof hfib P n j
      ((FreeGeneratorFaces.fixedFace (D C) (n + 1) i).toPrefunctor.mapPath q) t =
      family hcof hfib P (n + 1) (j ≫ P ◁ SSet.stdSimplex.δ i) q t :=
  family_face hcof hfib P n j i q t
example (i : Fin (n + 1)) (k : U ⟶ parameters P (n + 1))
    {X Y : degree (D C) (n + 1)} (q : Quiver.Path X Y)
    (t : ℕ → (U ⟶ WordSegment.obj)) :
    family hcof hfib P (n + 1) k ((degeneracyFunctor (D C) n i).toPrefunctor.mapPath q) t =
      family hcof hfib P n (k ≫ P ◁ OrdinaryBarFreeResolutionDegeneracyValues.sigma n i) q t :=
  family_degeneracy hcof hfib P n i k q t
-- Both local junction laws retain arbitrary whole prefix and suffix chains.
example {a d : D C} {X Y Z : degree (D C) (n + 1)}
    (q : chain hcof hfib U a X) (f : X ⟶ Y) (g : Y ⟶ Z)
    (t : U ⟶ WordSegment.obj) (r : chain hcof hfib U Z d) :
    OrdinaryBarWordChainFamily.family hcof hfib
      ((snoc hcof hfib P n j (snoc hcof hfib P n j q f (WordSegment.unitAt U)) g t).append r) =
      OrdinaryBarWordChainFamily.family hcof hfib ((snoc hcof hfib P n j q (f ≫ g) t).append r) :=
  unit_face hcof hfib P n j q f g t r
example {a d : D C} {X Y : degree (D C) (n + 1)}
    (q : chain hcof hfib U a X) (f : X ⟶ Y) (r : chain hcof hfib U Y d) :
    OrdinaryBarWordChainFamily.family hcof hfib
      ((snoc hcof hfib P n j q f (WordSegment.zeroAt U)).append r) =
      ParameterComposition.comp
        (OrdinaryBarWordChainFamily.family hcof hfib
          (snoc hcof hfib P n j q f (WordSegment.unitAt U)))
        (OrdinaryBarWordChainFamily.family hcof hfib r) := zero_face hcof hfib P n j q f r
end WholeParameters

section SmallParameters
variable {T U : SSet.{v}} (j : UniverseLift.obj.{max u v} T ⟶ parameters P n)
example {X Y : degree (D C) (n + 1)} (q : Quiver.Path X Y)
    (t : ℕ → (UniverseLift.obj.{max u v} T ⟶ WordSegment.obj)) :
    small hcof hfib X ⊗ T ⟶ small hcof hfib Y :=
  OrdinaryBarSmallFreeWordChainTransfer.family hcof hfib P n j q t
example (k : U ⟶ T) {X Y : degree (D C) (n + 1)} (q : Quiver.Path X Y)
    (t : ℕ → (UniverseLift.obj.{max u v} T ⟶ WordSegment.obj)) :
    OrdinaryBarSmallFreeWordChainTransfer.family hcof hfib P n (UniverseLift.map k ≫ j) q
        (fun r => UniverseLift.map k ≫ t r) =
      ParameterComposition.substitute k
        (OrdinaryBarSmallFreeWordChainTransfer.family hcof hfib P n j q t) :=
  OrdinaryBarSmallFreeWordChainTransfer.family_substitute hcof hfib P n j k q t
example (i : Fin (n + 2)) {X Y : degree (D C) (n + 2)} (q : Quiver.Path X Y)
    (t : ℕ → (UniverseLift.obj.{max u v} T ⟶ WordSegment.obj)) :
    OrdinaryBarSmallFreeWordChainTransfer.family hcof hfib P n j
      ((FreeGeneratorFaces.fixedFace (D C) (n + 1) i).toPrefunctor.mapPath q) t =
    OrdinaryBarSmallFreeWordChainTransfer.family hcof hfib P (n + 1)
      (j ≫ P ◁ SSet.stdSimplex.δ i) q t :=
  OrdinaryBarSmallFreeWordChainTransfer.family_face hcof hfib P n j i q t
end SmallParameters


section UnitElimination
open OrdinaryBarFreeWordChainTransfer
variable {U : SSet.{max u v}} (j : U ⟶ parameters P n)
example {a d : D C} {X Y : degree (D C) (n + 1)}
    (q : chain hcof hfib U a X) (f : X ⟶ Y) (t w : U ⟶ WordSegment.obj)
    (r : chain hcof hfib U Y d) :
    OrdinaryBarWordChainFamily.family hcof hfib
      ((snoc hcof hfib P n j (snoc hcof hfib P n j q f t)
        (FreeGeneratorCategories.identity (D C) (n + 1) Y) w).append r) =
      OrdinaryBarWordChainFamily.family hcof hfib
        ((snoc hcof hfib P n j q f (lift t w ≫ WordSegment.mul)).append r) :=
  interior_identity hcof hfib P n j q f t w r
example {X Y : degree (D C) (n + 1)} (q : Quiver.Path X Y)
    (t : ℕ → (U ⟶ RetractChainFamily.interval)) :
    family hcof hfib P n j q (fun k => t k ≫ WordSegment.letter) =
      OrdinaryBarFreeChainTransfer.family hcof hfib P n j q t :=
  family_ofInterval hcof hfib P n j q t
end UnitElimination

section SmallUnitElimination
variable {T : SSet.{v}} (j : UniverseLift.obj.{max u v} T ⟶ parameters P n)
example {a d : D C} {X Y : degree (D C) (n + 1)}
    (q : chain hcof hfib (UniverseLift.obj.{max u v} T) a X) (f : X ⟶ Y)
    (t w : UniverseLift.obj.{max u v} T ⟶ WordSegment.obj)
    (r : chain hcof hfib (UniverseLift.obj.{max u v} T) Y d) :
    OrdinaryBarWordChainFamily.smallFamily hcof hfib
      ((snoc hcof hfib P n j (snoc hcof hfib P n j q f t)
        (FreeGeneratorCategories.identity (D C) (n + 1) Y) w).append r) =
      OrdinaryBarWordChainFamily.smallFamily hcof hfib
        ((snoc hcof hfib P n j q f (lift t w ≫ WordSegment.mul)).append r) :=
  small_interior_identity hcof hfib P n j q f t w r
end SmallUnitElimination

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let modulePrefix := `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex
  let expected := #[`SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.WordRetractChainFamily,
    Name.str modulePrefix "OrdinaryBarWordChainFamily",
    Name.str modulePrefix "OrdinaryBarFreeWordChainTransfer",
    Name.str modulePrefix "OrdinaryBarSmallFreeWordChainTransfer"]
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
  unless modules.size == expected.size do throwError "Missing word chain transfer modules"
  logInfo m!"Word chain transfer audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
