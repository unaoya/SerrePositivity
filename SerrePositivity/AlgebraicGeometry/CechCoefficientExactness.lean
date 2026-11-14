module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFunctor
public import Mathlib.Algebra.Exact.Basic

/-!
概要：係数図式の自然同型に沿って増大 Čech の完全性を移す。
方針：各タプルの係数の同型を直積し、微分と可換な三つの同型を使う。
規約：零項を含む全タプル版を用いる。
使われ方：大域切断の局所化によるアフィン標準被覆の計算。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
variable {R ι : Type*} [CommRing R] [DecidableEq ι]
variable {D E : Finset ι ⥤ ModuleCat R}

/-- 係数の自然同型による、増大項を含む各 Čech 項の同型。 -/
def fullCechCoefficientEquiv (e : D ≅ E) (k : ℕ) :
    FullCechCochains D k ≃ₗ[R] FullCechCochains E k :=
  LinearEquiv.piCongrRight (fun t ↦ (e.app (cechTupleSupport t)).toLinearEquiv)

/-- 各項の同型は係数写像で与えられる。 -/
theorem fullCechCoefficientEquiv_toLinearMap (e : D ≅ E) (k : ℕ) :
    (fullCechCoefficientEquiv e k).toLinearMap = fullCechCochainsMap e.hom k := rfl

/-- 係数の自然同型は微分と可換。 -/
theorem fullCechCoefficientEquiv_differential (e : D ≅ E) (k : ℕ) :
    (fullCechDifferential E k).comp (fullCechCoefficientEquiv e k).toLinearMap =
      (fullCechCoefficientEquiv e (k + 1)).toLinearMap.comp (fullCechDifferential D k) :=
  (fullCechCochainsMap_comp_differential e.hom k).symm

/-- 自然同型に沿って増大項の微分の単射性を移す。 -/
theorem fullCechCoefficientEquiv_zero_injective (e : D ≅ E)
    (h : Function.Injective (fullCechDifferential D 0)) :
    Function.Injective (fullCechDifferential E 0) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := (fullCechCoefficientEquiv e 0).surjective x
  obtain ⟨b, rfl⟩ := (fullCechCoefficientEquiv e 0).surjective y
  congr 1
  apply h
  apply (fullCechCoefficientEquiv e 1).injective
  exact (LinearMap.congr_fun (fullCechCoefficientEquiv_differential e 0) a).symm.trans
    (hxy.trans (LinearMap.congr_fun (fullCechCoefficientEquiv_differential e 0) b))

/-- 自然同型に沿って増大 Čech の完全性を移す。 -/
theorem fullCechCoefficientEquiv_exact (e : D ≅ E) (k : ℕ)
    (h : Function.Exact (fullCechDifferential D k) (fullCechDifferential D (k + 1))) :
    Function.Exact (fullCechDifferential E k) (fullCechDifferential E (k + 1)) :=
  (Function.Exact.iff_of_ladder_linearEquiv
    (e₁ := fullCechCoefficientEquiv e k) (e₂ := fullCechCoefficientEquiv e (k + 1))
    (e₃ := fullCechCoefficientEquiv e (k + 2))
    (fullCechCoefficientEquiv_differential e k)
    (fullCechCoefficientEquiv_differential e (k + 1))).mpr h

end SerrePositivity.AlgebraicGeometry
