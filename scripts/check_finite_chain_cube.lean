import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarChainFamily

universe w v u uI
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.HomotopyFunctionComplex

-- The coordinate faces are actual maps, in every finite dimension, with no model structure.
example {n : ℕ} (j : Fin (n + 1)) (ε : Bool) :
    ParameterCube.face.{w} j ε ≫ ParameterCube.coordinate j =
      ParameterCube.endpoint ε (ParameterCube.obj n) :=
  ParameterCube.face_coordinate_same j ε

example {n : ℕ} (j : Fin (n + 1)) (ε : Bool) (i : Fin n) :
    ParameterCube.face.{w} j ε ≫ ParameterCube.coordinate (j.succAbove i) =
      ParameterCube.coordinate i :=
  ParameterCube.face_coordinate_other j ε i

-- A one face splits an arbitrary finite chain, retaining the entire parameter object.
example {ι : Type uI} (E K : ι → SSet.{w}) (s : ∀ i, K i ⟶ E i) (p : ∀ i, E i ⟶ K i)
    (H : ∀ i, SSet.Homotopy (𝟙 (E i)) (p i ≫ s i))
    (hH : ∀ i, (H i).h ≫ p i = fst (E i) RetractChainFamily.interval ≫ p i)
    {T : SSet.{w}} {a b c d : ι} (q : RetractChainFamily.Chain E T a b)
    (f : E b ⟶ E c) (r : RetractChainFamily.Chain E T c d) :
    RetractChainFamily.transfer E K s p H ((q.snoc f (RetractChainFamily.one T)).append r) =
      ParameterComposition.comp
        (RetractChainFamily.transfer E K s p H (q.snoc f (RetractChainFamily.zero T)))
        (RetractChainFamily.transfer E K s p H r) :=
  RetractChainFamily.one_face E K s p H hH q f r

section Actual
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

-- All finite dimensions give actual small families, with arbitrary source-model universes.
example (b : ℕ → Cᵒᵖ × C)
    (f : ∀ k, OrdinaryBarRetractSystem.ambient hcof hfib (b k) ⟶
      OrdinaryBarRetractSystem.ambient hcof hfib (b (k + 1))) (n : ℕ) :
    OrdinaryBarRetractSystem.small hcof hfib (b 0) ⊗ ParameterCube.obj.{v} n ⟶
      OrdinaryBarRetractSystem.small hcof hfib (b (n + 1)) :=
  OrdinaryBarChainFamily.cubeFamily hcof hfib b f n

-- The one-dimensional construction is the previously selected whole binary interval.
example (b : ℕ → Cᵒᵖ × C)
    (f : ∀ k, OrdinaryBarRetractSystem.ambient hcof hfib (b k) ⟶
      OrdinaryBarRetractSystem.ambient hcof hfib (b (k + 1))) :
    OrdinaryBarChainFamily.cubeFamily hcof hfib b f 1 =
      OrdinaryBarRetractSystem.small hcof hfib (b 0) ◁ ParameterCube.coordinate (0 : Fin 1) ≫
        (OrdinaryBarRetractSystem.smallTransferCompositionHomotopy hcof hfib (f 0) (f 1)).h :=
  OrdinaryBarChainFamily.cubeFamily_one hcof hfib b f

-- The zero junction law descends to the same original small universe.
example {T : SSet.{v}} {a b c d e : Cᵒᵖ × C}
    (q : OrdinaryBarChainFamily.chain hcof hfib (UniverseLift.obj.{max u v} T) a b)
    (f : OrdinaryBarRetractSystem.ambient hcof hfib b ⟶
      OrdinaryBarRetractSystem.ambient hcof hfib c)
    (g : OrdinaryBarRetractSystem.ambient hcof hfib c ⟶
      OrdinaryBarRetractSystem.ambient hcof hfib d)
    (t : UniverseLift.obj.{max u v} T ⟶ RetractChainFamily.interval)
    (r : OrdinaryBarChainFamily.chain hcof hfib (UniverseLift.obj.{max u v} T) d e) :
    OrdinaryBarChainFamily.smallFamily hcof hfib
        (((q.snoc f (RetractChainFamily.zero _)).snoc g t).append r) =
      OrdinaryBarChainFamily.smallFamily hcof hfib ((q.snoc (f ≫ g) t).append r) :=
  OrdinaryBarChainFamily.smallFamily_zero_face hcof hfib q f g t r

example {T : SSet.{v}} {a b c d : Cᵒᵖ × C}
    (q : OrdinaryBarChainFamily.chain hcof hfib (UniverseLift.obj.{max u v} T) a b)
    (f : OrdinaryBarRetractSystem.ambient hcof hfib b ⟶
      OrdinaryBarRetractSystem.ambient hcof hfib c)
    (r : OrdinaryBarChainFamily.chain hcof hfib (UniverseLift.obj.{max u v} T) c d) :
    OrdinaryBarChainFamily.smallFamily hcof hfib
        ((q.snoc f (RetractChainFamily.one _)).append r) =
      ParameterComposition.comp
        (OrdinaryBarChainFamily.smallFamily hcof hfib (q.snoc f (RetractChainFamily.zero _)))
        (OrdinaryBarChainFamily.smallFamily hcof hfib r) :=
  OrdinaryBarChainFamily.smallFamily_one_face hcof hfib q f r

-- Arbitrary small parameter maps, including every cube face, retain the full family.
example {T U : SSet.{v}} {b c : Cᵒᵖ × C} (j : U ⟶ T)
    (q : OrdinaryBarChainFamily.chain hcof hfib (UniverseLift.obj.{max u v} T) b c) :
    OrdinaryBarChainFamily.smallFamily hcof hfib (q.substitute (UniverseLift.map j)) =
      ParameterComposition.substitute j (OrdinaryBarChainFamily.smallFamily hcof hfib q) :=
  OrdinaryBarChainFamily.smallFamily_substitute hcof hfib j q
end Actual

-- Lifting a cube face preserves its selected endpoint without any large SSet model.
example {n : ℕ} (j : Fin (n + 1)) (ε : Bool) :
    UniverseLift.map.{max u v} (ParameterCube.face.{v} j ε) ≫
        OrdinaryBarChainFamily.liftParameter.{v, u} (ParameterCube.coordinate j) =
      if ε then RetractChainFamily.one (UniverseLift.obj.{max u v} (ParameterCube.obj n))
        else RetractChainFamily.zero (UniverseLift.obj.{max u v} (ParameterCube.obj n)) :=
  OrdinaryBarChainFamily.lifted_face_coordinate_same j ε

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.ParameterComposition,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RetractChainFamily,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.ParameterCube,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarChainFamily]
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
    throwError "Missing finite chain cube modules"
  logInfo m!"Finite chain cube audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
