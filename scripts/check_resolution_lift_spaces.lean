import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v u vH uH
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.Reedy

-- This applies to arbitrary model sources, including sources without any
-- specified functorial factorization and with only finite model limits.
example {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) :
    trivialFibrations SSet.{v} (ResolutionLiftSpace.projection X Y f) :=
  ResolutionLiftSpace.projection_trivialFibration hcof X Y f

-- Every strict resolution lift, including the ordinary arbitrary choice,
-- supplies an actual point in the very same derived lift space.
example {C : Type u} [Category.{v} C] [ModelCategory C]
    (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ ResolutionLiftSpace.obj X Y f :=
  ResolutionLiftSpace.ofLift (ResolutionObject.lift f)

-- Arbitrary higher boundary data extend, with their prescribed values intact.
example {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) (n : ℕ)
    (b : (SSet.boundary.{v} n).toSSet ⟶ ResolutionLiftSpace.obj X Y f) :
    ∃ e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ ResolutionLiftSpace.obj X Y f,
      (SSet.boundary n).ι ≫ e = b :=
  ResolutionLiftSpace.extension hcof X Y f _ b

example {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    (X Y : ResolutionObject C) (f : X.base ⟶ Y.base)
    (s t : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ ResolutionLiftSpace.obj X Y f) :
    ∃ e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ ResolutionLiftSpace.obj X Y f,
      SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫ e = s ∧
      SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) ≫ e = t :=
  ResolutionLiftSpace.interval hcof X Y f s t

-- The actual space is Kan and its actual projection is inverted by any Ho(SSet).
example {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
    {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
    [L.IsLocalization (weakEquivalences SSet.{v})]
    (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) :
    SSet.KanComplex (ResolutionLiftSpace.obj X Y f) ∧
      Nonempty (L.obj (ResolutionLiftSpace.obj X Y f) ≅
        L.obj (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))) :=
  ⟨ResolutionLiftSpace.kanComplex hcof hfib X Y f,
    ⟨ResolutionLiftSpace.localizationIso hcof L X Y f⟩⟩

-- The raw fibers vary strictly over B even without a model structure on C.
example {C : Type u} [Category.{v} C] (A : SimplexCategory ⥤ C) {X B : C}
    (a : A ⟶ (Functor.const SimplexCategory).obj X) (f : X ⟶ B) :
    Over B ⥤ SSet.{v} := LiftSpace.functor A a f

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.LiftSpace,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.LiftSpaceFunctor,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionLiftSpace]
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
  unless modules.size == expected.size do throwError "Some higher lift space modules were not audited"
  logInfo m!"Higher lift space audit passed: {count} declarations in {modules.size} modules, standard axioms only."
