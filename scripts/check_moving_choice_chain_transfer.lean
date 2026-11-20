import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarChoiceChainTransfer

universe w v u uI
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.HomotopyFunctionComplex

-- The general moving-edge face law has no model structure or Kan condition.
example {ι : Type uI} (E K : ι → SSet.{w}) (s : ∀ i, K i ⟶ E i) (p : ∀ i, E i ⟶ K i)
    (H : ∀ i, SSet.Homotopy (𝟙 (E i)) (p i ≫ s i)) {T : SSet.{w}} {a b c d e : ι}
    (q : RetractChainFamily.Chain E T a b) (f : E b ⊗ T ⟶ E c) (g : E c ⊗ T ⟶ E d)
    (t : T ⟶ RetractChainFamily.interval) (r : RetractChainFamily.Chain E T d e) :
    RetractChainFamily.transfer E K s p H
        (((q.familySnoc f (RetractChainFamily.zero T)).familySnoc g t).append r) =
      RetractChainFamily.transfer E K s p H
        ((q.familySnoc (ParameterComposition.comp f g) t).append r) :=
  RetractChainFamily.zero_family_face E K s p H q f g t r

section Actual
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
open OrdinaryBarChoiceChainTransfer

-- Every finite path in the actual choice category, with arbitrary independent junction parameters.
example {T : SSet.{max u v}} {X Y : choiceObject (C := C) hcof hfib T}
    (q : Quiver.Path X Y) (t : ℕ → (T ⟶ RetractChainFamily.interval)) :
    (ofPath hcof hfib q t).length = q.length := ofPath_length hcof hfib q t

-- The zero face composes actual category morphisms with moving full families.
example {T : SSet.{v}} {a d : Cᵒᵖ × C}
    {X Y Z : choiceObject (C := C) hcof hfib (UniverseLift.obj.{max u v} T)}
    (q : OrdinaryBarChainFamily.chain hcof hfib (UniverseLift.obj.{max u v} T) a X.base)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (t : UniverseLift.obj.{max u v} T ⟶ RetractChainFamily.interval)
    (r : OrdinaryBarChainFamily.chain hcof hfib (UniverseLift.obj.{max u v} T) Z.base d) :
    OrdinaryBarChainFamily.smallFamily hcof hfib
        ((snoc hcof hfib (snoc hcof hfib q f (RetractChainFamily.zero _)) g t).append r) =
      OrdinaryBarChainFamily.smallFamily hcof hfib ((snoc hcof hfib q (f ≫ g) t).append r) :=
  small_zero_face hcof hfib q f g t r

example {T : SSet.{v}} {a d : Cᵒᵖ × C}
    {X Y : choiceObject (C := C) hcof hfib (UniverseLift.obj.{max u v} T)}
    (q : OrdinaryBarChainFamily.chain hcof hfib (UniverseLift.obj.{max u v} T) a X.base)
    (f : X ⟶ Y)
    (r : OrdinaryBarChainFamily.chain hcof hfib (UniverseLift.obj.{max u v} T) Y.base d) :
    OrdinaryBarChainFamily.smallFamily hcof hfib
        ((snoc hcof hfib q f (RetractChainFamily.one _)).append r) =
      ParameterComposition.comp
        (OrdinaryBarChainFamily.smallFamily hcof hfib
          (snoc hcof hfib q f (RetractChainFamily.zero _)))
        (OrdinaryBarChainFamily.smallFamily hcof hfib r) :=
  small_one_face hcof hfib q f r

-- Arbitrary parameter restrictions substitute both the path morphisms and all junction coordinates.
example {T U : SSet.{v}} (j : U ⟶ T)
    {X Y : choiceObject (C := C) hcof hfib (UniverseLift.obj.{max u v} T)} (q : Quiver.Path X Y)
    (t : ℕ → (UniverseLift.obj.{max u v} T ⟶ RetractChainFamily.interval)) :
    smallPathFamily hcof hfib
        ((OrdinaryBarChoiceCategory.reindex hcof hfib (UniverseLift.map j)).toPrefunctor.mapPath q)
        (fun k => UniverseLift.map j ≫ t k) =
      ParameterComposition.substitute j (smallPathFamily hcof hfib q t) :=
  smallPathFamily_substitute hcof hfib j q t

example {T : SSet.{v}} (X : choiceObject (C := C) hcof hfib (UniverseLift.obj.{max u v} T))
    (t : ℕ → (UniverseLift.obj.{max u v} T ⟶ RetractChainFamily.interval)) :
    smallPathFamily hcof hfib (Quiver.Path.nil : Quiver.Path X X) t =
      ParameterComposition.const T (𝟙 (OrdinaryBarRetractSystem.small hcof hfib X.base)) :=
  smallPathFamily_nil hcof hfib X t

example {T : SSet.{v}}
    {X Y : choiceObject (C := C) hcof hfib (UniverseLift.obj.{max u v} T)} (f : X ⟶ Y)
    (t : ℕ → (UniverseLift.obj.{max u v} T ⟶ RetractChainFamily.interval)) :
    smallPathFamily hcof hfib f.toPath t =
      UniverseLift.lowerTensor (OrdinaryBarRetractSystem.transferFamily hcof hfib f.base f.extension) :=
  smallPathFamily_single hcof hfib f t
end Actual

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RetractChainFamily,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarChoiceChainTransfer]
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
    throwError "Missing moving choice chain transfer modules"
  logInfo m!"Moving choice chain transfer audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
