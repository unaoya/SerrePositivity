module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PairKoszulRing
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.IteratedKoszulRing

/-! # 元の二座標H⁰と一座標H⁰の反復の標準写像を保つ環同型 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable (R : Type u) [CommRing R]

/-- 元の二座標H⁰から反復したH⁰への標準比較射。 -/
def pairCompletionToIterated (f d : R) :
    letI := pairCompletionCommRing R f d
    letI := iteratedCompletionCommRing R f d
    PairCompletionH0 R f d →+* IteratedCompletionH0 R f d :=
  letI := iteratedCompletionCommRing R f d
  (pairCompletion_existsUnique_ringHom R f d (IteratedCompletionH0 R f d)
    (iteratedCompletionUnitRingHom R f d) (iteratedCompletion_isModuleComplete_unit_first R f d)
      (iteratedCompletion_isModuleComplete_unit_second R f d)).choose

/-- 比較射は元の環からの標準写像を保つ。 -/
theorem pairCompletionToIterated_comp_unit (f d : R) :
    letI := pairCompletionCommRing R f d
    letI := iteratedCompletionCommRing R f d
    (pairCompletionToIterated R f d).comp (pairCompletionUnitRingHom R f d) =
      iteratedCompletionUnitRingHom R f d :=
  letI := iteratedCompletionCommRing R f d
  (pairCompletion_existsUnique_ringHom R f d (IteratedCompletionH0 R f d)
    (iteratedCompletionUnitRingHom R f d) (iteratedCompletion_isModuleComplete_unit_first R f d)
      (iteratedCompletion_isModuleComplete_unit_second R f d)).choose_spec.1

/-- 反復したH⁰から元の二座標H⁰への標準比較射。 -/
def iteratedCompletionToPair (f d : R) :
    letI := pairCompletionCommRing R f d
    letI := iteratedCompletionCommRing R f d
    IteratedCompletionH0 R f d →+* PairCompletionH0 R f d :=
  letI := pairCompletionCommRing R f d
  (iteratedCompletion_existsUnique_ringHom R f d (PairCompletionH0 R f d)
    (pairCompletionUnitRingHom R f d) (pairCompletion_isModuleComplete_unit_first R f d)
      (pairCompletion_isModuleComplete_unit_second R f d)).choose

/-- 逆向きの比較射も標準写像を保つ。 -/
theorem iteratedCompletionToPair_comp_unit (f d : R) :
    letI := pairCompletionCommRing R f d
    letI := iteratedCompletionCommRing R f d
    (iteratedCompletionToPair R f d).comp (iteratedCompletionUnitRingHom R f d) =
      pairCompletionUnitRingHom R f d :=
  letI := pairCompletionCommRing R f d
  (iteratedCompletion_existsUnique_ringHom R f d (PairCompletionH0 R f d)
    (pairCompletionUnitRingHom R f d) (pairCompletion_isModuleComplete_unit_first R f d)
      (pairCompletion_isModuleComplete_unit_second R f d)).choose_spec.1

/-- 普遍性により、二座標H⁰上の比較の合成は恒等写像。 -/
theorem iteratedCompletionToPair_comp_toIterated (f d : R) :
    letI := pairCompletionCommRing R f d
    letI := iteratedCompletionCommRing R f d
    (iteratedCompletionToPair R f d).comp (pairCompletionToIterated R f d) =
      RingHom.id (PairCompletionH0 R f d) := by
  let := pairCompletionCommRing R f d
  let := iteratedCompletionCommRing R f d
  apply (pairCompletion_existsUnique_ringHom R f d (PairCompletionH0 R f d)
    (pairCompletionUnitRingHom R f d) (pairCompletion_isModuleComplete_unit_first R f d)
      (pairCompletion_isModuleComplete_unit_second R f d)).unique
  · rw [RingHom.comp_assoc, pairCompletionToIterated_comp_unit,
      iteratedCompletionToPair_comp_unit]
  · rfl

/-- 普遍性により、反復H⁰上の比較の合成も恒等写像。 -/
theorem pairCompletionToIterated_comp_toPair (f d : R) :
    letI := pairCompletionCommRing R f d
    letI := iteratedCompletionCommRing R f d
    (pairCompletionToIterated R f d).comp (iteratedCompletionToPair R f d) =
      RingHom.id (IteratedCompletionH0 R f d) := by
  let := pairCompletionCommRing R f d
  let := iteratedCompletionCommRing R f d
  apply (iteratedCompletion_existsUnique_ringHom R f d (IteratedCompletionH0 R f d)
    (iteratedCompletionUnitRingHom R f d) (iteratedCompletion_isModuleComplete_unit_first R f d)
      (iteratedCompletion_isModuleComplete_unit_second R f d)).unique
  · rw [RingHom.comp_assoc, iteratedCompletionToPair_comp_unit,
      pairCompletionToIterated_comp_unit]
  · rfl

/-- 元の二座標Koszul完備化のH⁰と一座標完備化の反復の環同型。 -/
def pairCompletionIteratedEquiv (f d : R) :
    letI := pairCompletionCommRing R f d
    letI := iteratedCompletionCommRing R f d
    PairCompletionH0 R f d ≃+* IteratedCompletionH0 R f d :=
  letI := pairCompletionCommRing R f d
  letI := iteratedCompletionCommRing R f d
  { pairCompletionToIterated R f d with
    invFun := iteratedCompletionToPair R f d
    left_inv := fun x ↦ congrArg (fun g ↦ g x) (iteratedCompletionToPair_comp_toIterated R f d)
    right_inv := fun x ↦ congrArg (fun g ↦ g x) (pairCompletionToIterated_comp_toPair R f d) }

/-- 環同型も、元の環からの標準写像を保つ。 -/
theorem pairCompletionIteratedEquiv_unit (f d r : R) :
    pairCompletionIteratedEquiv R f d (pairCompletionUnitRingHom R f d r) =
      iteratedCompletionUnitRingHom R f d r :=
  congrArg (fun g ↦ g r) (pairCompletionToIterated_comp_unit R f d)

end SerrePositivity.DerivedCompletion
