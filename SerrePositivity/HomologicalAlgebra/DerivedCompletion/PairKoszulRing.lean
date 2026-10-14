module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PairKoszulUnit
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerHomologyComplete

/-! # 実際の二座標Koszul完備化のH⁰の環と普遍性 -/

@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable (R : Type u) [CommRing R]

/-- 元の二座標Koszul塔の完備化の、実際の零次ホモロジー。 -/
abbrev PairCompletionH0 (f d : R) :=
  (koszulCompletionComplex R (pairKoszulCoordinates R f d)).homology 0

/-- 行列モデルのH⁰も、標準元について完備加群への反射となる。 -/
theorem pairTowerHomology_isCompleteModuleReflection (f d : R) :
    IsCompleteModuleReflection R (pairKoszulCoordinates R f d)
      (pairTowerShortComplex R f d).homology (pairTowerHomologyUnit R f d 1) where
  isComplete j := isModuleComplete_of_linearEquiv R (pairKoszulCoordinates R f d j)
    (PairCompletionH0 R f d) (pairTowerShortComplex R f d).homology
      (pairKoszulCompletionH0Equiv R f d)
        (koszulCompletionH0_isModuleComplete R (pairKoszulCoordinates R f d) j)
  universal N hN := pairTowerHomology_evaluation_bijective R f d N
    (by simpa only [pairKoszulCoordinates, Fin.snoc_apply_zero] using hN 0)
    (by simpa only [pairKoszulCoordinates, Fin.snoc_last] using hN (Fin.last 1))

/-- 元の実際のH⁰は、既存の標準元について完備加群への反射となる。 -/
theorem pairCompletionH0_isCompleteModuleReflection (f d : R) :
    IsCompleteModuleReflection R (pairKoszulCoordinates R f d) (PairCompletionH0 R f d)
      (koszulCompletionH0Unit R (pairKoszulCoordinates R f d) 1) :=
  (pairTowerHomology_isCompleteModuleReflection R f d).of_linearEquiv R
    (pairKoszulCompletionH0Equiv R f d).symm (by
      apply (pairKoszulCompletionH0Equiv R f d).injective
      rw [LinearEquiv.apply_symm_apply, pairKoszulCompletionH0Equiv_unit])

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

/-- 環としての標準写像は、既存のKoszul完備化のH⁰標準写像と一致する。 -/
theorem pairCompletionUnitRingHom_apply (f d r : R) :
    pairCompletionUnitRingHom R f d r = koszulCompletionH0Unit R (pairKoszulCoordinates R f d) r :=
  (pairCompletionH0_isCompleteModuleReflection R f d).unitRingHom_eq_linearMap
    (koszulCompletionH0Unit R (pairKoszulCoordinates R f d)) rfl r

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

/-- 両座標の完備性を、列の各座標についての条件へ戻す。 -/
theorem pairKoszulCoordinates_isModuleComplete (f d : R) (N : ModuleCat.{u} R)
    (hf : IsModuleComplete R f N) (hd : IsModuleComplete R d N) :
    ∀ j, IsModuleComplete R (pairKoszulCoordinates R f d j) N := by
  intro j
  refine Fin.lastCases ?_ (fun i ↦ ?_) j
  · simpa only [pairKoszulCoordinates, Fin.snoc_last] using hd
  · simpa only [pairKoszulCoordinates, Fin.snoc_castSucc] using hf

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

end SerrePositivity.DerivedCompletion
