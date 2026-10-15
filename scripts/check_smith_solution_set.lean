import SerrePositivity.HomotopicalAlgebra.Foundations
import SerrePositivity.Spectra.General.Foundations
import SerrePositivity.Spectra.StageTwo
import Lean.Util.CollectAxioms

universe w t u v
noncomputable section
open CategoryTheory SerrePositivity.Smith

-- There is deliberately no ModelCategory assumption on C and no W.IsSmall.
variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  [IsAccessibleCategory.{w} (Arrow C)]
  [IsAccessibleCategory.{w} (arrowProperty W).FullSubcategory]
  [(arrowInclusion W).IsAccessible.{w}]

example : SolutionSetCondition.{w} (arrowInclusion W) := solutionSetCondition W
example (i : Arrow C) : Type w := solutionIndex W i
example (i : Arrow C) (j : solutionIndex W i) : W (solutionArrow W i j).obj.hom :=
  (solutionArrow W i j).property

example {A B X Y : C} (i : A ⟶ B) (f : X ⟶ Y) (hf : W f)
    (a : A ⟶ X) (b : B ⟶ Y) (sq : CommSq a i f b) :
    ∃ (j : solutionIndex W (Arrow.mk i))
      (g : (solutionArrow W (Arrow.mk i) j).obj ⟶ Arrow.mk f),
      (solutionSquare W (Arrow.mk i) j).left ≫ g.left = a ∧
      (solutionSquare W (Arrow.mk i) j).right ≫ g.right = b :=
  solutionSquare_factor_components W (Arrow.mk i) (Arrow.mk f) hf
    (Arrow.homMk a b sq.w)

example (i f : Arrow C) (hf : W f.hom) (sq : i ⟶ f) :
    ∃ (j : solutionIndex W i) (g : (solutionArrow W i j).obj ⟶ f),
      solutionSquare W i j ≫ g = sq := solutionSquare_factor W i f hf sq

-- The indexing universe t is independent of the solution-set universe w.
example {ι : Type t} [Small.{w} ι] (a : ι → Arrow C) :
    (solutionTargets W a).IsSmall.{w} := inferInstance
example {ι : Type t} (a : ι → Arrow C) : solutionTargets W a ≤ W :=
  solutionTargets_le W a
example {ι : Type t} (a : ι → Arrow C) (k : ι)
    (f : Arrow C) (hf : W f.hom) (sq : a k ⟶ f) :
    ∃ g : Arrow C, solutionTargets W a g.hom ∧
      ∃ (p : a k ⟶ g) (q : g ⟶ f), p ≫ q = sq :=
  solutionTargets_factor W a k f hf sq

-- A complete R0 consumer: W need not be small and C has no model structure.
example (I : MorphismProperty C) [I.IsSmall.{w}] :
    ∃ J : MorphismProperty C, J.IsSmall.{w} ∧ J ≤ W ∧
      ∀ (i f : Arrow C), I i.hom → W f.hom → ∀ sq : i ⟶ f,
        ∃ g : Arrow C, J g.hom ∧ ∃ (p : i ⟶ g) (q : g ⟶ f), p ≫ q = sq :=
  ⟨solutionTargetsForClass W I, inferInstance, solutionTargetsForClass_le W I,
    fun i f hi hf sq ↦ solutionTargetsForClass_factor W I i f hi hf sq⟩

example {ι : Type t} [IsEmpty ι] (a : ι → Arrow C) : solutionTargets W a ≤ ⊥ := by
  rintro _ _ _ ⟨x⟩
  exact False.elim (isEmptyElim x.1 : False)

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless env.header.modules[idx.toNat]!.module ==
        `SerrePositivity.HomotopicalAlgebra.Smith.SolutionSet do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "No Smith solution-set declarations audited"
  logInfo m!"Smith solution-set audit passed: {count} declarations, standard axioms only."
