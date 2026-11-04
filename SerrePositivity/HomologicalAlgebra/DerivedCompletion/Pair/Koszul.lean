module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Pair.Iteration
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Tower.HolimModel
public import SerrePositivity.HomologicalAlgebra.Complex.Cone
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.KoszulModel
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Koszul.Tower
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Presentation
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Tower.Maps
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletion.Reconstruction

/-! # 二つの座標の完備化の H⁰ の環

## 概要

二つの座標の完備化の H⁰ `PairCompletionH0` を、一つの座標の完備化の反復 `IteratedCompletionH0` を `R` 加群として見たものと定め、両座標で完備な加群への反映（`pairCompletionH0_isCompleteModuleReflection`）から環構造・代数構造と普遍性（`pairCompletionCommRing`・`pairCompletionUnitRingHom`・`pairCompletionLift`）を与える。反復した環との環同型（`pairCompletionIteratedEquiv`）も示す。

## 方針

API はすべて反映を通して述べ、`PairCompletionH0` の中身には触れない。環同型は両方向の持ち上げの合成が恒等であることを普遍性の一意性で確かめる。

## 規約

`pairKoszulCoordinates`・`PairCompletionH0`・`pairCompletionH0Unit`・`pairCompletionCommRing`・`pairCompletionUnitRingHom`・`pairCompletionIteratedEquiv` は BhattScholze が使うので名前を変えない。2b の B4（段階 3）で定義を Koszul 塔の H⁰ から一つの座標の反復へ移し、二つの座標の Koszul 塔の行列模型（旧 `Pair/Tower`・`PairKoszul{Stage, Transition, Comparison, Product, Cone, Unit}`）を削除した（refactor-plan §3.5.3）。ファイル名は import 行を変えないために残した。旧 `PairKoszulRing`・`PairIterationComparison`。

## 使われ方

`PDCompletion`、`PairZeroCompletion`、`CompletedAlgebraH0`、BhattScholze。
-/

@[expose] public noncomputable section

universe u

section PairCompletionRingPart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable (R : Type u) [CommRing R]

/-- 二つの座標の完備化の H⁰。一つ目の座標の完備化の H⁰ を、二つ目の座標の像について再び完備化したもの（`IteratedCompletionH0`）を `R` 加群として見る。 -/
def PairCompletionH0 (f d : R) : ModuleCat.{u} R :=
  letI := iteratedCompletionCommRing R f d
  letI := iteratedCompletionAlgebra R f d
  ModuleCat.of R (IteratedCompletionH0 R f d)

/-- 二座標H⁰への線形な標準写像。利用側はこの名前を通して使う。 -/
def pairCompletionH0Unit (f d : R) : R →ₗ[R] PairCompletionH0 R f d :=
  letI := iteratedCompletionCommRing R f d
  letI := iteratedCompletionAlgebra R f d
  LinearMap.toSpanSingleton R (PairCompletionH0 R f d) (1 : IteratedCompletionH0 R f d)

/-- 二座標H⁰は、標準元について両座標で完備な加群への反映となる（`iteratedCompletion_isCompleteModuleReflection`）。 -/
theorem pairCompletionH0_isCompleteModuleReflection (f d : R) :
    IsCompleteModuleReflection R (pairKoszulCoordinates R f d) (PairCompletionH0 R f d)
      (pairCompletionH0Unit R f d 1) := by
  letI := iteratedCompletionCommRing R f d
  letI := iteratedCompletionAlgebra R f d
  have h1 : pairCompletionH0Unit R f d 1 = (1 : IteratedCompletionH0 R f d) := one_smul R _
  rw [h1]
  exact iteratedCompletion_isCompleteModuleReflection R f d

/-- 元の加法群とR作用を保つ、実際の二座標H⁰の可換環構造。 -/
@[instance_reducible] def pairCompletionCommRing (f d : R) : CommRing (PairCompletionH0 R f d) :=
  (pairCompletionH0_isCompleteModuleReflection R f d).commRing

/-- 実際の二座標H⁰のR代数構造。 -/
@[instance_reducible] def pairCompletionAlgebra (f d : R) :
    letI := pairCompletionCommRing R f d; Algebra R (PairCompletionH0 R f d) :=
  (pairCompletionH0_isCompleteModuleReflection R f d).algebra

/-- 既存のH⁰標準写像を環準同型として実現する。 -/
def pairCompletionUnitRingHom (f d : R) :
    letI := pairCompletionCommRing R f d; R →+* PairCompletionH0 R f d :=
  (pairCompletionH0_isCompleteModuleReflection R f d).unitRingHom

/-- 環としての標準写像は、線形な標準写像と一致する。 -/
theorem pairCompletionUnitRingHom_apply (f d r : R) :
    pairCompletionUnitRingHom R f d r = pairCompletionH0Unit R f d r :=
  (pairCompletionH0_isCompleteModuleReflection R f d).unitRingHom_eq_linearMap
    (pairCompletionH0Unit R f d) rfl r

/-- 実際の二座標H⁰は、最初の元fについて導来完備。 -/
theorem pairCompletionH0_isModuleComplete_first (f d : R) :
    IsModuleComplete R f (PairCompletionH0 R f d) := by
  simpa only [pairKoszulCoordinates, Fin.snoc_apply_zero] using
    (pairCompletionH0_isCompleteModuleReflection R f d).isComplete 0

/-- 実際の二座標H⁰は、二つ目の元dについて導来完備。 -/
theorem pairCompletionH0_isModuleComplete_second (f d : R) :
    IsModuleComplete R d (PairCompletionH0 R f d) := by
  simpa only [pairKoszulCoordinates, Fin.snoc_last] using
    (pairCompletionH0_isCompleteModuleReflection R f d).isComplete (Fin.last 1)

/-- 構成した代数の標準写像は、既存の標準環準同型と一致する。 -/
theorem pairCompletion_algebraMap (f d r : R) :
    letI := pairCompletionCommRing R f d
    letI := pairCompletionAlgebra R f d
    algebraMap R (PairCompletionH0 R f d) r = pairCompletionUnitRingHom R f d r := rfl

/-- 構成した代数構造は、標準環準同型から得る構造に一致する。 -/
theorem pairCompletionAlgebra_eq_toAlgebra (f d : R) :
    letI := pairCompletionCommRing R f d
    pairCompletionAlgebra R f d = (pairCompletionUnitRingHom R f d).toAlgebra := by
  let := pairCompletionCommRing R f d
  exact Algebra.algebra_ext _ _ (fun r ↦ pairCompletion_algebraMap R f d r)

/-- 標準環準同型による作用の下で、fについて導来完備。 -/
theorem pairCompletion_isModuleComplete_unit_first (f d : R) :
    letI := pairCompletionCommRing R f d
    letI := (pairCompletionUnitRingHom R f d).toAlgebra
    IsModuleComplete R f
      (@ModuleCat.of R _ (PairCompletionH0 R f d) _
        (@Algebra.toModule R (PairCompletionH0 R f d) _ _ inferInstance)) := by
  let := pairCompletionCommRing R f d
  exact Eq.mp (congrArg (fun a : Algebra R (PairCompletionH0 R f d) ↦
    letI := a
    IsModuleComplete R f
      (@ModuleCat.of R _ (PairCompletionH0 R f d) _
        (@Algebra.toModule R (PairCompletionH0 R f d) _ _ a)))
      (pairCompletionAlgebra_eq_toAlgebra R f d)) (pairCompletionH0_isModuleComplete_first R f d)

/-- 標準環準同型による作用の下で、dについて導来完備。 -/
theorem pairCompletion_isModuleComplete_unit_second (f d : R) :
    letI := pairCompletionCommRing R f d
    letI := (pairCompletionUnitRingHom R f d).toAlgebra
    IsModuleComplete R d
      (@ModuleCat.of R _ (PairCompletionH0 R f d) _
        (@Algebra.toModule R (PairCompletionH0 R f d) _ _ inferInstance)) := by
  let := pairCompletionCommRing R f d
  exact Eq.mp (congrArg (fun a : Algebra R (PairCompletionH0 R f d) ↦
    letI := a
    IsModuleComplete R d
      (@ModuleCat.of R _ (PairCompletionH0 R f d) _
        (@Algebra.toModule R (PairCompletionH0 R f d) _ _ a)))
      (pairCompletionAlgebra_eq_toAlgebra R f d)) (pairCompletionH0_isModuleComplete_second R f d)

/-- 実際の二座標H⁰から、両座標で完備なR代数への延長は一意。 -/
theorem pairCompletion_existsUnique_algHom (f d : R)
    (T : Type u) [CommRing T] [Algebra R T]
    (hf : IsModuleComplete R f (ModuleCat.of R T))
    (hd : IsModuleComplete R d (ModuleCat.of R T)) :
    letI := pairCompletionCommRing R f d
    letI := pairCompletionAlgebra R f d
    ∃! _g : PairCompletionH0 R f d →ₐ[R] T, True :=
  (pairCompletionH0_isCompleteModuleReflection R f d).existsUnique_algHom T
    (pairKoszulCoordinates_isModuleComplete R f d (ModuleCat.of R T) hf hd)

/-- 両方の座標について導来完備な離散 `R` 代数への代数写像の延長（`pairCompletion_existsUnique_algHom` の写像）。 -/
def pairCompletionLiftAlgHom (f d : R) (T : Type u) [CommRing T] [Algebra R T]
    (hf : IsModuleComplete R f (ModuleCat.of R T))
    (hd : IsModuleComplete R d (ModuleCat.of R T)) :
    letI := pairCompletionCommRing R f d
    letI := pairCompletionAlgebra R f d
    PairCompletionH0 R f d →ₐ[R] T :=
  (pairCompletionH0_isCompleteModuleReflection R f d).liftAlgHom T
    (pairKoszulCoordinates_isModuleComplete R f d (ModuleCat.of R T) hf hd)

/-- 任意の環準同型は、実際の二座標H⁰の標準写像から一意に延長する。 -/
theorem pairCompletion_existsUnique_ringHom (f d : R)
    (T : Type u) [CommRing T] (g : R →+* T)
    (hf : letI := g.toAlgebra; IsModuleComplete R f (ModuleCat.of R T))
    (hd : letI := g.toAlgebra; IsModuleComplete R d (ModuleCat.of R T)) :
    letI := pairCompletionCommRing R f d
    ∃! h : PairCompletionH0 R f d →+* T, h.comp (pairCompletionUnitRingHom R f d) = g := by
  let := g.toAlgebra
  let := pairCompletionCommRing R f d
  let := pairCompletionAlgebra R f d
  obtain ⟨h, _, hu⟩ := pairCompletion_existsUnique_algHom R f d T hf hd
  refine ⟨h.toRingHom, ?_, ?_⟩
  · ext r
    exact h.commutes r
  · intro k hk
    let k' : PairCompletionH0 R f d →ₐ[R] T :=
      { k with commutes' := fun r ↦ congrArg (fun m : R →+* T ↦ m r) hk }
    exact congrArg AlgHom.toRingHom (hu k' trivial)

/-- 標準写像に沿った、両方の座標で導来完備な離散環への環準同型の延長
（`pairCompletion_existsUnique_ringHom` の写像）。 -/
def pairCompletionLift (f d : R) (T : Type u) [CommRing T] (g : R →+* T)
    (hf : letI := g.toAlgebra; IsModuleComplete R f (ModuleCat.of R T))
    (hd : letI := g.toAlgebra; IsModuleComplete R d (ModuleCat.of R T)) :
    letI := pairCompletionCommRing R f d
    PairCompletionH0 R f d →+* T := by
  letI := g.toAlgebra
  letI := pairCompletionCommRing R f d
  letI := pairCompletionAlgebra R f d
  exact (pairCompletionLiftAlgHom R f d T hf hd).toRingHom

/-- 延長は標準写像との合成で元の環準同型に戻る。 -/
theorem pairCompletionLift_comp (f d : R) (T : Type u) [CommRing T] (g : R →+* T)
    (hf : letI := g.toAlgebra; IsModuleComplete R f (ModuleCat.of R T))
    (hd : letI := g.toAlgebra; IsModuleComplete R d (ModuleCat.of R T)) :
    letI := pairCompletionCommRing R f d
    (pairCompletionLift R f d T g hf hd).comp (pairCompletionUnitRingHom R f d) = g := by
  letI := g.toAlgebra
  letI := pairCompletionCommRing R f d
  letI := pairCompletionAlgebra R f d
  ext r
  exact (pairCompletionLiftAlgHom R f d T hf hd).commutes r

end SerrePositivity.DerivedCompletion

end PairCompletionRingPart

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
  pairCompletionLift R f d (IteratedCompletionH0 R f d)
    (iteratedCompletionUnitRingHom R f d) (iteratedCompletion_isModuleComplete_unit_first R f d)
      (iteratedCompletion_isModuleComplete_unit_second R f d)

/-- 比較射は元の環からの標準写像を保つ。 -/
theorem pairCompletionToIterated_comp_unit (f d : R) :
    letI := pairCompletionCommRing R f d
    letI := iteratedCompletionCommRing R f d
    (pairCompletionToIterated R f d).comp (pairCompletionUnitRingHom R f d) =
      iteratedCompletionUnitRingHom R f d :=
  letI := iteratedCompletionCommRing R f d
  pairCompletionLift_comp R f d (IteratedCompletionH0 R f d)
    (iteratedCompletionUnitRingHom R f d) (iteratedCompletion_isModuleComplete_unit_first R f d)
      (iteratedCompletion_isModuleComplete_unit_second R f d)

/-- 反復したH⁰から元の二座標H⁰への標準比較射。 -/
def iteratedCompletionToPair (f d : R) :
    letI := pairCompletionCommRing R f d
    letI := iteratedCompletionCommRing R f d
    IteratedCompletionH0 R f d →+* PairCompletionH0 R f d :=
  letI := pairCompletionCommRing R f d
  iteratedCompletionLift R f d (PairCompletionH0 R f d)
    (pairCompletionUnitRingHom R f d) (pairCompletion_isModuleComplete_unit_first R f d)
      (pairCompletion_isModuleComplete_unit_second R f d)

/-- 逆向きの比較射も標準写像を保つ。 -/
theorem iteratedCompletionToPair_comp_unit (f d : R) :
    letI := pairCompletionCommRing R f d
    letI := iteratedCompletionCommRing R f d
    (iteratedCompletionToPair R f d).comp (iteratedCompletionUnitRingHom R f d) =
      pairCompletionUnitRingHom R f d :=
  letI := pairCompletionCommRing R f d
  iteratedCompletionLift_comp R f d (PairCompletionH0 R f d)
    (pairCompletionUnitRingHom R f d) (pairCompletion_isModuleComplete_unit_first R f d)
      (pairCompletion_isModuleComplete_unit_second R f d)

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

/- API を述べ終えたので、`PairCompletionH0` とその単位を外からは展開させない。利用側の定義的な比較が
反復した H⁰ の中まで降りて重くならないようにする（BhattScholze の具体的な PD 完備化の証明）。 -/
attribute [irreducible] SerrePositivity.DerivedCompletion.PairCompletionH0
  SerrePositivity.DerivedCompletion.pairCompletionH0Unit
