module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.KoszulModel
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Pair.Koszul

/-! # 二つの座標の完備化と一つの座標の完備化の反復

## 概要

一つの座標の H⁰ を二度当てた環 `IteratedCompletionH0` とその標準写像を作り、元の二つの座標の H⁰ と、標準写像を保つ環同型で一致することを示す（`pairCompletionToIterated`・`iteratedCompletionToPair`）。

## 方針

両方向の写像を普遍性から作り、合成が恒等であることを単位で確かめる。

## 規約

旧 `IteratedKoszulRing`・`PairIterationComparison`（2b の B の Pair の置き換えの土台）。

## 使われ方

`PDCompletion`。
-/

@[expose] public noncomputable section

universe u

section IteratedKoszulRingPart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable (R : Type u) [CommRing R]

/-- fの一座標完備化のH⁰を、dの標準像について再び完備化したH⁰。 -/
abbrev IteratedCompletionH0 (f d : R) :=
  letI := principalCompletionCommRing R f
  PrincipalCompletionH0 (PrincipalCompletionH0 R f) (principalCompletionUnitRingHom R f d)

/-- 反復したH⁰の可換環構造。 -/
@[instance_reducible] def iteratedCompletionCommRing (f d : R) :
    CommRing (IteratedCompletionH0 R f d) :=
  letI := principalCompletionCommRing R f
  principalCompletionCommRing (PrincipalCompletionH0 R f) (principalCompletionUnitRingHom R f d)

/-- 反復したH⁰への標準環準同型。 -/
def iteratedCompletionUnitRingHom (f d : R) :
    letI := iteratedCompletionCommRing R f d; R →+* IteratedCompletionH0 R f d :=
  letI := principalCompletionCommRing R f
  (principalCompletionUnitRingHom (PrincipalCompletionH0 R f)
    (principalCompletionUnitRingHom R f d)).comp (principalCompletionUnitRingHom R f)

/-- 反復したH⁰のR代数構造は、一座標の元の加群作用を制限したもの。 -/
@[instance_reducible] def iteratedCompletionAlgebra (f d : R) :
    letI := iteratedCompletionCommRing R f d; Algebra R (IteratedCompletionH0 R f d) := by
  letI := principalCompletionCommRing R f
  letI := principalCompletionAlgebra R f
  letI := iteratedCompletionCommRing R f d
  letI := principalCompletionAlgebra (PrincipalCompletionH0 R f)
    (principalCompletionUnitRingHom R f d)
  letI : Module R (IteratedCompletionH0 R f d) :=
    Module.compHom (IteratedCompletionH0 R f d) (principalCompletionUnitRingHom R f)
  exact Algebra.ofModule
    (fun r x y ↦ by
      change ((principalCompletionUnitRingHom R f r) • x) * y =
        (principalCompletionUnitRingHom R f r) • (x * y)
      exact smul_mul_assoc _ _ _)
    (fun r x y ↦ by
      change x * ((principalCompletionUnitRingHom R f r) • y) =
        (principalCompletionUnitRingHom R f r) • (x * y)
      exact mul_smul_comm _ _ _)

/-- 反復した代数の標準写像は、二つの既存H⁰標準写像の合成。 -/
theorem iteratedCompletion_algebraMap (f d r : R) :
    letI := iteratedCompletionCommRing R f d
    letI := iteratedCompletionAlgebra R f d
    algebraMap R (IteratedCompletionH0 R f d) r = iteratedCompletionUnitRingHom R f d r := by
  rfl

/-- 二度目の主元完備化は、最初の元fについての導来完備性を保つ。 -/
theorem iteratedCompletion_isModuleComplete_first (f d : R) :
    letI := iteratedCompletionCommRing R f d
    letI := iteratedCompletionAlgebra R f d
    IsModuleComplete R f (ModuleCat.of R (IteratedCompletionH0 R f d)) := by
  let := principalCompletionCommRing R f
  let := principalCompletionAlgebra R f
  let := iteratedCompletionCommRing R f d
  let := iteratedCompletionAlgebra R f d
  exact principalCompletionH0_isModuleComplete_of_other R (PrincipalCompletionH0 R f) f
    (principalCompletionUnitRingHom R f d) (principalCompletionH0_isModuleComplete R f)

/-- 反復したH⁰は、二つ目の元dについても導来完備。 -/
theorem iteratedCompletion_isModuleComplete_second (f d : R) :
    letI := iteratedCompletionCommRing R f d
    letI := iteratedCompletionAlgebra R f d
    IsModuleComplete R d (ModuleCat.of R (IteratedCompletionH0 R f d)) := by
  let := principalCompletionCommRing R f
  let := principalCompletionAlgebra R f
  let := iteratedCompletionCommRing R f d
  let := principalCompletionAlgebra (PrincipalCompletionH0 R f)
    (principalCompletionUnitRingHom R f d)
  let := iteratedCompletionAlgebra R f d
  let _ : IsScalarTower R (PrincipalCompletionH0 R f) (IteratedCompletionH0 R f d) :=
    ⟨fun r s x ↦ by
      change (r • s) • x = (principalCompletionUnitRingHom R f r) • (s • x)
      rw [Algebra.smul_def (R := R) (A := PrincipalCompletionH0 R f)]
      exact mul_smul (principalCompletionUnitRingHom R f r) s x⟩
  exact (isModuleComplete_algebraMap_iff R (PrincipalCompletionH0 R f) d
    (IteratedCompletionH0 R f d)).mp
      (principalCompletionH0_isModuleComplete (PrincipalCompletionH0 R f)
        (principalCompletionUnitRingHom R f d))

/-- 反復した代数構造は、標準環準同型から得られる代数構造と一致する。 -/
theorem iteratedCompletionAlgebra_eq_toAlgebra (f d : R) :
    letI := iteratedCompletionCommRing R f d
    iteratedCompletionAlgebra R f d = (iteratedCompletionUnitRingHom R f d).toAlgebra := by
  let := iteratedCompletionCommRing R f d
  exact Algebra.algebra_ext _ _ (fun r ↦ iteratedCompletion_algebraMap R f d r)

/-- 標準環準同型による作用の下で、fについて導来完備。 -/
theorem iteratedCompletion_isModuleComplete_unit_first (f d : R) :
    letI := iteratedCompletionCommRing R f d
    letI := (iteratedCompletionUnitRingHom R f d).toAlgebra
    IsModuleComplete R f (ModuleCat.of R (IteratedCompletionH0 R f d)) := by
  let := iteratedCompletionCommRing R f d
  exact Eq.mp (congrArg (fun a : Algebra R (IteratedCompletionH0 R f d) ↦
    letI := a
    IsModuleComplete R f (ModuleCat.of R (IteratedCompletionH0 R f d)))
      (iteratedCompletionAlgebra_eq_toAlgebra R f d))
        (iteratedCompletion_isModuleComplete_first R f d)

/-- 標準環準同型による作用の下で、dについて導来完備。 -/
theorem iteratedCompletion_isModuleComplete_unit_second (f d : R) :
    letI := iteratedCompletionCommRing R f d
    letI := (iteratedCompletionUnitRingHom R f d).toAlgebra
    IsModuleComplete R d (ModuleCat.of R (IteratedCompletionH0 R f d)) := by
  let := iteratedCompletionCommRing R f d
  exact Eq.mp (congrArg (fun a : Algebra R (IteratedCompletionH0 R f d) ↦
    letI := a
    IsModuleComplete R d (ModuleCat.of R (IteratedCompletionH0 R f d)))
      (iteratedCompletionAlgebra_eq_toAlgebra R f d))
        (iteratedCompletion_isModuleComplete_second R f d)

/-- 二座標に導来完備な離散環への任意の写像は、反復したH⁰から一意に延長する。 -/
theorem iteratedCompletion_existsUnique_ringHom (f d : R)
    (T : Type u) [CommRing T] (g : R →+* T)
    (hf : letI := g.toAlgebra; IsModuleComplete R f (ModuleCat.of R T))
    (hd : letI := g.toAlgebra; IsModuleComplete R d (ModuleCat.of R T)) :
    letI := iteratedCompletionCommRing R f d
    ∃! h : IteratedCompletionH0 R f d →+* T,
      h.comp (iteratedCompletionUnitRingHom R f d) = g := by
  let := principalCompletionCommRing R f
  let := principalCompletionAlgebra R f
  let := iteratedCompletionCommRing R f d
  obtain ⟨h₁, hh₁, hu₁⟩ := principalCompletion_existsUnique_ringHom R f T g hf
  have hd' : letI := (h₁.comp (principalCompletionUnitRingHom R f)).toAlgebra
      IsModuleComplete R d (ModuleCat.of R T) := by
    exact Eq.mpr (congrArg (fun q : R →+* T ↦
      letI := q.toAlgebra
      IsModuleComplete R d (ModuleCat.of R T)) hh₁) hd
  have hdS := (isModuleComplete_ringHom_comp_iff R (PrincipalCompletionH0 R f) T
    (principalCompletionUnitRingHom R f) h₁ d).mpr hd'
  obtain ⟨h₂, hh₂, hu₂⟩ := principalCompletion_existsUnique_ringHom
    (PrincipalCompletionH0 R f) (principalCompletionUnitRingHom R f d) T h₁ hdS
  refine ⟨h₂, ?_, ?_⟩
  · change h₂.comp ((principalCompletionUnitRingHom (PrincipalCompletionH0 R f)
      (principalCompletionUnitRingHom R f d)).comp (principalCompletionUnitRingHom R f)) = g
    rw [← RingHom.comp_assoc, hh₂, hh₁]
  · intro k hk
    apply hu₂ k
    apply hu₁
    change (k.comp (principalCompletionUnitRingHom (PrincipalCompletionH0 R f)
      (principalCompletionUnitRingHom R f d))).comp (principalCompletionUnitRingHom R f) = g
    rw [RingHom.comp_assoc]
    exact hk

end SerrePositivity.DerivedCompletion

end IteratedKoszulRingPart

section PairIterationComparisonPart

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

end PairIterationComparisonPart
