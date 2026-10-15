import SerrePositivity.HomotopicalAlgebra.Smith.GeneratedWeakReflection
import Lean.Util.CollectAxioms

universe w v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.Smith

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

example (F : C ⥤ D) [F.Full] [F.Faithful] (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [F.IsCardinalAccessible κ] (X : C) [IsCardinalPresentable (F.obj X) κ] :
    IsCardinalPresentable X κ := presentable_of_accessible_fullyFaithful F κ X

example {P : ObjectProperty C} {κ : Cardinal.{w}} [Fact κ.IsRegular]
    [IsCardinalLocallyPresentable C κ] (r : PresentableWeakReflection P κ)
    [HasCardinalFilteredColimits.{w} P.FullSubcategory κ] [P.ι.IsCardinalAccessible κ] :
    IsCardinalAccessibleCategory P.FullSubcategory κ := r.isCardinalAccessibleCategory

-- A genuine bounded weak reflection: the identity on the whole category.
example (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    PresentableWeakReflection (⊤ : ObjectProperty C) κ where
  R := 𝟭 C
  unit := 𝟙 _
  obj_mem _ := trivial
  preservesPresentable := inferInstance
  factor _ f := ⟨f, Category.id_comp _⟩

-- No model structure: extension is derived from the specified generated factorization.
example (I : MorphismProperty C)
    (d : MorphismProperty.FunctorialFactorizationData I.rlp.llp I.rlp)
    {f p : Arrow C} (hp : I.rlp p.hom) (φ : f ⟶ p) :
    ∃ ψ : (GeneratedWeakReflection.rightFactor I d).obj f ⟶ p,
      (GeneratedWeakReflection.unit I d).app f ≫ ψ = φ :=
  GeneratedWeakReflection.factor I d hp φ

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Smith.PresentableFullInclusion,
    `SerrePositivity.HomotopicalAlgebra.Smith.PresentableWeakReflection,
    `SerrePositivity.HomotopicalAlgebra.Smith.GeneratedWeakReflection]
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
  if modules.size != expected.size then throwError "Not all weak-reflection modules were audited"
  logInfo m!"Presentable weak-reflection audit passed: {count} declarations in 3 modules, standard axioms only."
