module

public import SerrePositivity.AlgebraicGeometry.CechConeHomologyExactness
public import SerrePositivity.AlgebraicGeometry.CochainComplexOfExactness
public import Mathlib.Algebra.Homology.QuasiIso

/-!
概要：実際の射の準同型性から、既存の明示的な cone の完全性を得る。
方針：既存のサイクルの境界への反映と持ち上げを零次・正次数に使う。
規約：基底環と加群の宇宙を分け、導来関手の層の H との比較を行わない。
使われ方：射影四角形に用いる共通アフィン細分の cochain map の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R : Type v} [CommRing R]
variable (A B : CochainComplex (ModuleCat.{u} R) ℕ) (f : A ⟶ B)

/-- 全次数で準同型な元の射の、既存の自然数添字の cone は完全。 -/
theorem cechRefinementCone_acyclic_of_quasiIso (hf : ∀ q, QuasiIsoAt f q) :
    (cechRefinementCone A B f).Acyclic := by
  have hzero : Function.Bijective (ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R) (.up ℕ) 0 0 1).map f)).hom := by
    have h := hf 0
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff] at h
    exact (ConcreteCategory.isIso_iff_bijective _).mp h
  have hpos (n : ℕ) : Function.Bijective (ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R) (.up ℕ)
        n (n + 1) (n + 2)).map f)).hom := by
    have h := hf (n + 1)
    rw [quasiIsoAt_iff' f n (n + 1) (n + 2)
      (ComplexShape.prev_eq' (.up ℕ) (by rfl)) (ComplexShape.next_eq' (.up ℕ) (by rfl)),
      ShortComplex.quasiIso_iff] at h
    exact (ConcreteCategory.isIso_iff_bijective _).mp h
  apply cochainComplexOf_acyclic_of_injective_exact
  · intro n
    apply ModuleCat.hom_ext
    exact cechRefinementConeDifferential_squared A B f n
  · apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    have ha : (A.d 0 1).hom x = 0 := neg_eq_zero.mp (congrArg Prod.snd hx)
    have hb : (f.f 0).hom x = 0 := congrArg Prod.fst hx
    obtain ⟨a, he⟩ := cechCycles_boundary_of_homology_injective
      (A.sc' 0 0 1) (B.sc' 0 0 1)
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R) (.up ℕ) 0 0 1).map f)
      hzero.1 x ha ⟨0, by
        change (B.d 0 0).hom 0 = (f.f 0).hom x
        simpa only [map_zero] using hb.symm⟩
    change (A.d 0 0).hom a = x at he
    have hz : (A.d 0 0).hom a = 0 := by
      rw [A.shape 0 0 (by simp)]
      rfl
    exact he.symm.trans hz
  · intro n x
    constructor
    · exact cechRefinementCone_cycle_boundary_of_homology A B f hzero.2 hpos n x
    · rintro ⟨y, rfl⟩
      exact LinearMap.congr_fun (cechRefinementConeDifferential_squared A B f n) y

end SerrePositivity.AlgebraicGeometry
