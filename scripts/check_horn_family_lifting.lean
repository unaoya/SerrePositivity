import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.KanHornFamilyLifting
import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarUnitCoherence
import Lean.Util.CollectAxioms

universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open SerrePositivity.SimplicialModel

section AnyDimension
variable (K : SSet.{v}) {n : ℕ} (i : Fin (n + 2))
  (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))
  {U V : SSet.{v}} (j : U ⟶ V) [Mono j]
  (b : V ⟶ (ihom (SSet.horn (n + 1) i).toSSet).obj K)
  (a : U ⟶ (ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).obj K)
  (ha : a ≫ KanHornFamilyLifting.restriction K i = j ≫ b)

-- The boundary family may vary over V, with no constancy hypothesis.
example : ∃ e : V ⟶ (ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).obj K,
    j ≫ e = a ∧ e ≫ KanHornFamilyLifting.restriction K i = b :=
  ⟨(KanHornFamilyLifting.relativeLift K i hK j b a ha).val,
    (KanHornFamilyLifting.relativeLift K i hK j b a ha).property⟩
example : SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ◁ j ≫
    KanHornFamilyLifting.relativeFamily K i hK j b a ha = uncurry a :=
  KanHornFamilyLifting.relativeFamily_earlier K i hK j b a ha
example : (SSet.horn (n + 1) i).ι ▷ V ≫
    KanHornFamilyLifting.relativeFamily K i hK j b a ha = uncurry b :=
  KanHornFamilyLifting.relativeFamily_boundary K i hK j b a ha
example : KanHornFamilyLifting.uniformFamily K i hK (j ≫ b) =
    SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ◁ j ≫
      KanHornFamilyLifting.uniformFamily K i hK b :=
  KanHornFamilyLifting.uniformFamily_naturality K i hK b j
-- Uniform filling is natural under arbitrary parameter maps, including nonmonomorphisms.
example {A B : SSet.{v}} (r : A ⟶ B)
    (b₀ : B ⟶ (ihom (SSet.horn (n + 1) i).toSSet).obj K) :
    KanHornFamilyLifting.uniform K i hK (r ≫ b₀) =
      r ≫ KanHornFamilyLifting.uniform K i hK b₀ :=
  KanHornFamilyLifting.uniform_naturality K i hK b₀ r
end AnyDimension

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
local notation "Q" => CategoryTheory.Functor.obj (ihom T) K
local notation "e" => OrdinaryBarUnitCoherence.leftData hcof hfib P j f cX c

-- Retain the actual previously chosen native unit tetrahedron when the horn family varies.
example {V : SSet.{v}} (p : SSet.stdSimplex.obj (SimplexCategory.mk 0) ⟶ V) [Mono p]
    (b : V ⟶ (ihom (SSet.horn 3 3).toSSet).obj Q)
    (ha : RelativeChoiceSpace.name (e).tetrahedron ≫ KanHornFamilyLifting.restriction Q 3 = p ≫ b) :
    ∃ a : V ⟶ (ihom (SSet.stdSimplex.obj (SimplexCategory.mk 3))).obj Q,
      p ≫ a = RelativeChoiceSpace.name (e).tetrahedron ∧
        a ≫ KanHornFamilyLifting.restriction Q 3 = b := by
  have hQ : SSet.modelCategoryQuillen.J.rlp (terminal.from Q) :=
    SimplexParameterHom.native_kan T K
      (SimplexParameterHom.native_kan (small hcof hfib X) (small hcof hfib Y)
        (OrdinaryBarSmallReference.value_kan hcof hfib Y))
  let l := KanHornFamilyLifting.relativeLift Q 3 hQ p b
    (RelativeChoiceSpace.name (e).tetrahedron) ha
  exact ⟨l.val, l.property⟩
end Native

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.KanHornFamilyLifting
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless env.header.modules[idx.toNat]!.module == expected do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
  unless count > 0 do throwError "Missing horn family lifting module"
  logInfo m!"Horn family lifting audit passed: {count} declarations, standard axioms only."
