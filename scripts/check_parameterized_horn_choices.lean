import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.ParameterizedHornChoices
import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarUnitCoherence
import Lean.Util.CollectAxioms

universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity.SimplicialModel KanComparisonTriangle

section AnyDimension
variable (T K : SSet.{v}) {n : ℕ} {i : Fin (n + 2)}
  (faces : ∀ (j : Fin (n + 2)) (_ : j ≠ i),
    SSet.stdSimplex.obj (SimplexCategory.mk n) ⟶ (ihom T).obj K)
  (hf : SSet.horn.IsCompatible faces)

-- Actual arbitrary-dimensional faces, including whole extra parameter families.
example {L : SSet.{v}} (c : L ⟶ ParameterizedHornChoices.obj T K faces hf)
    (j : Fin (n + 2)) (hj : j ≠ i) :
    SSet.stdSimplex.δ j ▷ L ≫ ParameterizedHornChoices.family T K faces hf c =
      fst (SSet.stdSimplex.obj (SimplexCategory.mk n)) L ≫ faces j hj :=
  ParameterizedHornChoices.family_face T K faces hf c j hj
example (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K)) {U V : SSet.{v}}
    (j : U ⟶ V) [Mono j] (c : U ⟶ ParameterizedHornChoices.obj T K faces hf) :
    ∃ d : V ⟶ ParameterizedHornChoices.obj T K faces hf, j ≫ d = c ∧
      SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ◁ j ≫
        ParameterizedHornChoices.family T K faces hf d =
          ParameterizedHornChoices.family T K faces hf c ∧
      (Functor.const (Over T)ᵒᵖ).map j ≫ ParameterizedHornChoices.naturalFamily T K faces hf d =
        ParameterizedHornChoices.naturalFamily T K faces hf c :=
  ParameterizedHornChoices.relative_extension T K faces hf hK j c
example (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))
    (a b : SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ⟶ (ihom T).obj K)
    (ha : ∀ j hj, SSet.stdSimplex.δ j ≫ a = faces j hj)
    (hb : ∀ j hj, SSet.stdSimplex.δ j ≫ b = faces j hj) :
    RelativeChoiceSpace.FixedBoundaryHomotopy (SSet.horn (n + 1) i).ι hf.desc a b :=
  ParameterizedHornChoices.fixedFacesComparison T K faces hf hK a b ha hb
end AnyDimension

private lemma tetrahedronFaces {T K : SSet.{v}} {f g h z : T ⟶ K}
    (F : SSet.Homotopy f z) (G : SSet.Homotopy g z) (H : SSet.Homotopy h z)
    (a : Data F G) (b : Data F H) (c : Data G H)
    (d : KanComparisonTetrahedron.Filler F G H a b c) :
    ∀ j hj, SSet.stdSimplex.δ j ≫ d.tetrahedron =
      KanComparisonTetrahedron.hornFaces F G H a b c j hj := by
  intro j hj
  fin_cases j
  · exact d.face_zero
  · exact d.face_one
  · exact d.face_two
  · exact (hj rfl).elim

section Native
open SerrePositivity.HomotopyFunctionComplex
open OrdinaryBarFreeResolutionSeed OrdinaryBarRetractSystem OrdinaryBarRelativeHomDescent
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) {T : SSet.{v}} {X Y : D C}
  (j : UniverseLift.obj.{max u v} T ⟶ P)
  (f : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
  (cX : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P X X)
  (c : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P X Y)

local notation "K" => CategoryTheory.Functor.obj (ihom (small hcof hfib X)) (small hcof hfib Y)
local notation "F" => OrdinaryBarUnitTriangles.root hcof hfib P j f c
local notation "G" => OrdinaryBarUnitTriangles.leftIntermediate hcof hfib P j f cX c
local notation "a" => OrdinaryBarUnitTriangles.leftOutgoing hcof hfib P j f cX c
local notation "b" => ComparisonTriangleDegeneracy.diagonal F
local notation "d" => OrdinaryBarUnitTriangles.leftReturn hcof hfib P j f cX c
local notation "e" => OrdinaryBarUnitCoherence.leftData hcof hfib P j f cX c
local notation "faces" => KanComparisonTetrahedron.hornFaces F G F a b d
local notation "hf" => KanComparisonTetrahedron.hornCompatible F G F a b d

-- The actual old native unit tetrahedron is included and recovers unchanged.
example : ParameterizedHornChoices.family T K faces hf
    (ParameterizedHornChoices.ofFiller T K faces hf (e).tetrahedron
      (tetrahedronFaces F G F a b d e)) =
    SSet.stdSimplex.obj (SimplexCategory.mk 3) ◁ RelativeChoiceSpace.pointUnitIso.hom ≫
      (ρ_ (SSet.stdSimplex.obj (SimplexCategory.mk 3))).hom ≫ (e).tetrahedron :=
  ParameterizedHornChoices.ofFiller_family T K faces hf (e).tetrahedron
    (tetrahedronFaces F G F a b d e)
example : ParameterizedHornChoices.naturalPoint T K faces hf (e).tetrahedron
    (tetrahedronFaces F G F a b d e) ≫
      ParameterChoiceDiagram.projection T K (SSet.horn 3 3).ι (hf).desc = 𝟙 _ :=
  ParameterizedHornChoices.naturalPoint_projection T K faces hf (e).tetrahedron
    (tetrahedronFaces F G F a b d e)
end Native

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.ParameterizedHornChoices
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless env.header.modules[idx.toNat]!.module == expected do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
  unless count > 0 do throwError "Missing parameterized horn choice module"
  logInfo m!"Parameterized horn choice audit passed: {count} declarations, standard axioms only."
