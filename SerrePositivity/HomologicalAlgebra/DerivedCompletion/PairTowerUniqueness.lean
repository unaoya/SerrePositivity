module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PairTowerEvaluation

/-! # 二座標行列モデルから完備加群への延長の一意性

一座標のサイクルを二通りに埋め込み、任意の二座標サイクルをその和へ分解する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable (R : Type u) [CommRing R]

/-- dの一座標サイクルを二座標モデルへ含める。 -/
def pairTowerCyclesFromD (f d : R) : PrincipalTowerCycles R d →ₗ[R] PairTowerCycles R f d where
  toFun c := ⟨(c.val.1, (c.val.2, 0)), by
    change adicRecurrenceMap (1 : R) c.val.1 - principalPowerMap R d c.val.2 -
      principalPowerMap R f 0 = 0
    rw [map_zero, sub_zero]
    exact c.property⟩
  map_add' x y := by apply Subtype.ext; ext <;> simp
  map_smul' r x := by apply Subtype.ext; ext <;> simp

/-- fの一座標サイクルを二座標モデルへ含める。 -/
def pairTowerCyclesFromF (f d : R) : PrincipalTowerCycles R f →ₗ[R] PairTowerCycles R f d where
  toFun c := ⟨(c.val.1, (0, c.val.2)), by
    change adicRecurrenceMap (1 : R) c.val.1 - principalPowerMap R d 0 -
      principalPowerMap R f c.val.2 = 0
    rw [map_zero, sub_zero]
    exact c.property⟩
  map_add' x y := by apply Subtype.ext; ext <;> simp
  map_smul' r x := by apply Subtype.ext; ext <;> simp

/-- dの境界は二座標の通常の境界へ送られる。 -/
theorem pairTowerCyclesFromD_boundary (f d : R) (z : ℕ → R) :
    pairTowerCyclesFromD R f d (principalTowerBoundary R d z) =
      pairTowerBoundary R f d ((z, 0), 0) := by
  apply Subtype.ext
  simp [pairTowerCyclesFromD, principalTowerBoundary, principalTowerBoundaryPair,
    pairTowerBoundary, pairTowerBoundaryTriple]

/-- fの境界は二座標の通常の境界へ送られる。 -/
theorem pairTowerCyclesFromF_boundary (f d : R) (z : ℕ → R) :
    pairTowerCyclesFromF R f d (principalTowerBoundary R f z) =
      pairTowerBoundary R f d ((0, z), 0) := by
  apply Subtype.ext
  simp [pairTowerCyclesFromF, principalTowerBoundary, principalTowerBoundaryPair,
    pairTowerBoundary, pairTowerBoundaryTriple]

/-- 任意の二座標サイクルは、一座標サイクルの二つの像の和。 -/
theorem pairTowerCycles_decomposition (f d : R) (c : PairTowerCycles R f d) :
    c = pairTowerCyclesFromD R f d
      (principalTowerCycleOfCoordinates R d (c.val.1 0) c.val.2.1) +
    pairTowerCyclesFromF R f d (principalTowerCycleOfCoordinates R f 0 c.val.2.2) := by
  apply pairTowerCycles_ext R f d
  · simp [pairTowerCyclesFromD, pairTowerCyclesFromF, principalTowerCycleOfCoordinates,
      principalTowerPrefix]
  · simp [pairTowerCyclesFromD, pairTowerCyclesFromF, principalTowerCycleOfCoordinates]

/-- dの一座標のサイクルの商から二座標のサイクルの商への写像。 -/
def pairTowerQuotientFromD (f d : R) :
    (PrincipalTowerCycles R d ⧸ (principalTowerBoundary R d).range) →ₗ[R]
      (PairTowerCycles R f d ⧸ (pairTowerBoundary R f d).range) :=
  (principalTowerBoundary R d).range.mapQ (pairTowerBoundary R f d).range
    (pairTowerCyclesFromD R f d) (by
      rintro c ⟨z, rfl⟩
      exact ⟨((z, 0), 0), (pairTowerCyclesFromD_boundary R f d z).symm⟩)

/-- fの一座標のサイクルの商から二座標のサイクルの商への写像。 -/
def pairTowerQuotientFromF (f d : R) :
    (PrincipalTowerCycles R f ⧸ (principalTowerBoundary R f).range) →ₗ[R]
      (PairTowerCycles R f d ⧸ (pairTowerBoundary R f d).range) :=
  (principalTowerBoundary R f).range.mapQ (pairTowerBoundary R f d).range
    (pairTowerCyclesFromF R f d) (by
      rintro c ⟨z, rfl⟩
      exact ⟨((0, z), 0), (pairTowerCyclesFromF_boundary R f d z).symm⟩)

/-- dの主元反射加群から二座標の商への標準写像。 -/
def pairTowerReflectionFromD (f d : R) :
    PrincipalReflectionModule R d →ₗ[R]
      (PairTowerCycles R f d ⧸ (pairTowerBoundary R f d).range) :=
  (pairTowerQuotientFromD R f d).comp (principalTowerCycleQuotientEquiv R d).symm.toLinearMap

/-- fの主元反射加群から二座標の商への標準写像。 -/
def pairTowerReflectionFromF (f d : R) :
    PrincipalReflectionModule R f →ₗ[R]
      (PairTowerCycles R f d ⧸ (pairTowerBoundary R f d).range) :=
  (pairTowerQuotientFromF R f d).comp (principalTowerCycleQuotientEquiv R f).symm.toLinearMap

/-- dの反射からの写像は標準元を保つ。 -/
theorem pairTowerReflectionFromD_unit (f d : R) :
    pairTowerReflectionFromD R f d (principalReflectionUnit R d) =
      Submodule.Quotient.mk (pairTowerConstantCycle R f d 1) := by
  rw [← principalTowerCycleQuotientEquiv_unit R d]
  change pairTowerQuotientFromD R f d
    ((principalTowerCycleQuotientEquiv R d).symm ((principalTowerCycleQuotientEquiv R d) _)) = _
  rw [LinearEquiv.symm_apply_apply]
  change Submodule.Quotient.mk (pairTowerCyclesFromD R f d
    (principalTowerCycleOfCoordinates R d 1 0)) = _
  congr 1
  apply pairTowerCycles_ext R f d
  · rfl
  · rfl

/-- fの反射からの写像は標準元を保つ。 -/
theorem pairTowerReflectionFromF_unit (f d : R) :
    pairTowerReflectionFromF R f d (principalReflectionUnit R f) =
      Submodule.Quotient.mk (pairTowerConstantCycle R f d 1) := by
  rw [← principalTowerCycleQuotientEquiv_unit R f]
  change pairTowerQuotientFromF R f d
    ((principalTowerCycleQuotientEquiv R f).symm ((principalTowerCycleQuotientEquiv R f) _)) = _
  rw [LinearEquiv.symm_apply_apply]
  change Submodule.Quotient.mk (pairTowerCyclesFromF R f d
    (principalTowerCycleOfCoordinates R f 1 0)) = _
  congr 1
  apply pairTowerCycles_ext R f d
  · rfl
  · rfl

/-- 標準元を零へ送る完備加群への写像は零。 -/
theorem pairTowerQuotientHom_eq_zero (f d : R) (N : ModuleCat.{u} R)
    (hf : IsModuleComplete R f N) (hd : IsModuleComplete R d N)
    (g : (PairTowerCycles R f d ⧸ (pairTowerBoundary R f d).range) →ₗ[R] N)
    (hg : g (Submodule.Quotient.mk (pairTowerConstantCycle R f d 1)) = 0) : g = 0 := by
  have hD : g.comp (pairTowerReflectionFromD R f d) = 0 :=
    principalReflectionHom_eq_zero R d N hd _ (by
      change g (pairTowerReflectionFromD R f d (principalReflectionUnit R d)) = 0
      rw [pairTowerReflectionFromD_unit, hg])
  have hF : g.comp (pairTowerReflectionFromF R f d) = 0 :=
    principalReflectionHom_eq_zero R f N hf _ (by
      change g (pairTowerReflectionFromF R f d (principalReflectionUnit R f)) = 0
      rw [pairTowerReflectionFromF_unit, hg])
  have hzD (c : PrincipalTowerCycles R d) :
      g (Submodule.Quotient.mk (pairTowerCyclesFromD R f d c)) = 0 := by
    have h := LinearMap.congr_fun hD
      (principalTowerCycleQuotientEquiv R d (Submodule.Quotient.mk c))
    simpa [pairTowerReflectionFromD, pairTowerQuotientFromD] using h
  have hzF (c : PrincipalTowerCycles R f) :
      g (Submodule.Quotient.mk (pairTowerCyclesFromF R f d c)) = 0 := by
    have h := LinearMap.congr_fun hF
      (principalTowerCycleQuotientEquiv R f (Submodule.Quotient.mk c))
    simpa [pairTowerReflectionFromF, pairTowerQuotientFromF] using h
  apply LinearMap.ext
  intro q
  obtain ⟨c, rfl⟩ := (pairTowerBoundary R f d).range.mkQ_surjective q
  rw [pairTowerCycles_decomposition R f d c]
  change g ((pairTowerBoundary R f d).range.mkQ (_ + _)) = 0
  simp only [map_add, Submodule.mkQ_apply, hzD, hzF, add_zero]

/-- ホモロジー上でも、標準元を零へ送る完備加群への写像は零。 -/
theorem pairTowerHomologyHom_eq_zero (f d : R) (N : ModuleCat.{u} R)
    (hf : IsModuleComplete R f N) (hd : IsModuleComplete R d N)
    (g : (pairTowerShortComplex R f d).homology →ₗ[R] N)
    (hg : g (pairTowerHomologyUnit R f d 1) = 0) : g = 0 := by
  let e := pairTowerHomologyQuotientEquiv R f d
  have hu : e.symm (Submodule.Quotient.mk (pairTowerConstantCycle R f d 1)) =
      pairTowerHomologyUnit R f d 1 := by
    apply e.injective
    rw [LinearEquiv.apply_symm_apply]
    exact (pairTowerHomologyQuotientEquiv_unit R f d 1).symm
  have hQ : g.comp e.symm.toLinearMap = 0 :=
    pairTowerQuotientHom_eq_zero R f d N hf hd _ (by
      change g (e.symm (Submodule.Quotient.mk (pairTowerConstantCycle R f d 1))) = 0
      rw [hu, hg])
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun hQ (e x)
  simpa using h

/-- 二座標モデルのH⁰からの線形延長は、標準元の像で一意に決まる。 -/
theorem pairTowerHomology_evaluation_bijective (f d : R) (N : ModuleCat.{u} R)
    (hf : IsModuleComplete R f N) (hd : IsModuleComplete R d N) :
    Function.Bijective (fun g : (pairTowerShortComplex R f d).homology →ₗ[R] N ↦
      g (pairTowerHomologyUnit R f d 1)) := by
  constructor
  · intro g h he
    apply sub_eq_zero.mp
    exact pairTowerHomologyHom_eq_zero R f d N hf hd (g - h) (sub_eq_zero.mpr he)
  · intro t
    exact pairTowerHomologyEvaluation_exists R f d N hf hd t

end SerrePositivity.DerivedCompletion
