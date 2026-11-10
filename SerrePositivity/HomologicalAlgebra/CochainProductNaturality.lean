module

public import SerrePositivity.HomologicalAlgebra.CochainProductClass
import all SerrePositivity.HomologicalAlgebra.CochainProductClass

/-!
# 余鎖積のコホモロジーへの自然性

## 概要
積を保つ余鎖写像は、コホモロジー上でも積を保つ。

## 方針
各コホモロジー類を余輪体で表し、写像と積を代表元で計算する。

## 規約
余輪体の条件は隣の次数への微分で書く。

## 使われ方
pd de Rham 総複体の二つの射影。
-/

public noncomputable section

open CategoryTheory HomologicalComplex

universe u

namespace SerrePositivity.HomologicalAlgebra.CochainProduct

variable {R : Type u} [CommRing R] {K L : CochainComplex (ModuleCat.{u} R) ℕ}

private theorem closedClass_surjective (n : ℕ) (x : K.homology n) :
    ∃ (z : K.X n) (hz : K.d n (n+1) z = 0), closedClass n z hz = x := by
  obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ n)).mp inferInstance x
  let z := K.iCycles n y
  have hz : K.d n (n+1) z = 0 := by
    have h := ConcreteCategory.congr_hom (K.iCycles_d n (n+1)) y
    simpa only [ConcreteCategory.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply, z] using h
  refine ⟨z, hz, ?_⟩
  unfold closedClass
  congr 1
  apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
  exact K.i_cyclesMk z _ _ hz

private theorem map_closed (f : K ⟶ L) {n : ℕ} {z : K.X n} (h : K.d n (n+1) z = 0) :
    L.d n (n+1) (f.f n z) = 0 := by
  have hz := ConcreteCategory.congr_hom (f.comm n (n+1)) z
  simp only [ConcreteCategory.comp_apply, h, map_zero] at hz
  exact hz

private theorem homologyMap_closedClass (f : K ⟶ L) {n : ℕ} (z : K.X n)
    (h : K.d n (n+1) z = 0) :
    homologyMap f n (closedClass n z h) = closedClass n (f.f n z) (map_closed f h) := by
  let y := K.cyclesMk z (n+1) (CochainComplex.next ℕ n) h
  have hy := ConcreteCategory.congr_hom (homologyπ_naturality f n) y
  simp only [ConcreteCategory.comp_apply] at hy
  change homologyMap f n (closedClass n z h) = L.homologyπ n (cyclesMap f n y) at hy
  rw [hy]
  unfold closedClass
  congr 1
  apply (ModuleCat.mono_iff_injective (L.iCycles n)).mp inferInstance
  have h' := ConcreteCategory.congr_hom (cyclesMap_i f n) y
  simp only [ConcreteCategory.comp_apply] at h'
  change L.iCycles n (cyclesMap f n y) = f.f n (K.iCycles n y) at h'
  rw [h', show K.iCycles n y = z from K.i_cyclesMk z _ _ h]
  exact (L.i_cyclesMk _ _ _ _).symm

/-- 積を保つ余鎖写像はコホモロジー上でも積を保つ。 -/
theorem onHomology_natural (M : CochainProduct K) (N : CochainProduct L) (f : K ⟶ L)
    (hf : ∀ i j (x : K.X i) (y : K.X j),
      f.f (i+j) (M.mul i j x y) = N.mul i j (f.f i x) (f.f j y))
    {i j : ℕ} (a : K.homology i) (b : K.homology j) :
    homologyMap f (i+j) (M.onHomology a b) =
      N.onHomology (homologyMap f i a) (homologyMap f j b) := by
  obtain ⟨x, hx, rfl⟩ := closedClass_surjective i a
  obtain ⟨y, hy, rfl⟩ := closedClass_surjective j b
  have hxy : K.d (i+j) (i+j+1) (M.mul i j x y) = 0 := by
    rw [M.leibniz, hx, hy, map_zero, LinearMap.zero_apply, map_zero, smul_zero, add_zero]
    exact cast_zero' (K := K) (by omega)
  have hxy' : L.d (i+j) (i+j+1) (N.mul i j (f.f i x) (f.f j y)) = 0 := by
    rw [← hf]
    exact map_closed f hxy
  rw [onHomology_closedClass M x y hx hy hxy, homologyMap_closedClass,
    homologyMap_closedClass, homologyMap_closedClass,
    onHomology_closedClass N _ _ (map_closed f hx) (map_closed f hy) hxy']
  congr 1
  exact hf i j x y

end SerrePositivity.HomologicalAlgebra.CochainProduct
