module

public import SerrePositivity.CommutativeAlgebra.DeRham.CompletedCoefficient

/-!
# 完備多項式 de Rham 複体

## 概要
完備形式の係数に完備偏微分を作用させ、外積で次数を一つ上げる。

## 方針
完備多項式環と外冪とのテンソル積で計算する。偏微分の可換性と外積の反交換性を使う。

## 規約
完備微分は元の係数環上で線形。

## 使われ方
Hodge–Tate 比較の完備形式側と、整係数 de Rham 複体。
-/

public section
noncomputable section

universe u

open scoped TensorProduct

namespace SerrePositivity.DeRham

variable (k : Type u) [CommRing k] (T : Type u) [Fintype T] [DecidableEq T] (p : ℕ)

local notation "E[" i "]" => (⋀[k]^i (T → k))
local notation "P" => Poly k T
local notation "Q" => completedPoly k T p

private def completedFormsCoeffEquiv (i : ℕ) :
    completedForms k T p i ≃ₗ[k] Q ⊗[k] E[i] :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange k P Q Q E[i]).restrictScalars k

private theorem completedFormsCoeffEquiv_unit_tmul (i : ℕ) (f : P) (v : E[i]) :
    completedFormsCoeffEquiv k T p i (completedFormsUnit k T p i (f ⊗ₜ[k] v)) =
      algebraMap P Q f ⊗ₜ[k] v := by
  change TensorProduct.AlgebraTensorModule.cancelBaseChange k P Q Q E[i] (1 ⊗ₜ[P] (f ⊗ₜ[k] v)) = _
  rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, Algebra.smul_def, mul_one]

private def rawD (i : ℕ) : (Q ⊗[k] E[i]) →ₗ[k] (Q ⊗[k] E[i + 1]) :=
  ∑ t : T, TensorProduct.map (completedPderiv k T p t)
    (wedgeOne k (T → k) i ((exteriorPower.oneEquiv k (T → k)).symm (Pi.single t 1)))

private def completedDLinear (i : ℕ) : completedForms k T p i →ₗ[k] completedForms k T p (i + 1) :=
  (completedFormsCoeffEquiv k T p (i + 1)).symm.toLinearMap ∘ₗ rawD k T p i ∘ₗ
    (completedFormsCoeffEquiv k T p i).toLinearMap

/-- 概要：完備形式上の de Rham 微分。
方針：完備偏微分と、対応する変数の一次形式の左外積をテンソルする。
規約：元の係数環上の線形写像を加法写像として読む。
使われ方：完備多項式 de Rham 複体。 -/
def completedDeRhamD (i : ℕ) : completedForms k T p i →+ completedForms k T p (i + 1) :=
  (completedDLinear k T p i).toAddMonoidHom

private theorem completedFormsCoeffEquiv_d (i : ℕ) (ω : completedForms k T p i) :
    completedFormsCoeffEquiv k T p (i + 1) (completedDeRhamD k T p i ω) =
      rawD k T p i (completedFormsCoeffEquiv k T p i ω) :=
  LinearEquiv.apply_symm_apply _ _

/-- 完備微分は完備化単位に沿って多項式の de Rham 微分を延長する。 -/
theorem completedDeRhamD_unit (i : ℕ) (ω : forms k T i) :
    completedDeRhamD k T p i (completedFormsUnit k T p i ω) =
      completedFormsUnit k T p (i + 1) (deRhamD k T i ω) := by
  induction ω using TensorProduct.inductionOn with
  | add a b ha hb => simp [map_add, ha, hb]
  | tmul f v =>
      apply (completedFormsCoeffEquiv k T p (i + 1)).injective
      rw [completedFormsCoeffEquiv_d, completedFormsCoeffEquiv_unit_tmul]
      simp only [rawD, deRhamD, deRhamDLinear, LinearMap.toAddMonoidHom_coe,
        LinearMap.sum_apply, TensorProduct.map_tmul, map_sum, completedFormsCoeffEquiv_unit_tmul,
        completedPderiv_unit]
      rfl

omit [Fintype T] [DecidableEq T] in
private theorem wedgeOne_sq (i : ℕ) (a : T → k) (b : E[i]) :
    let e := (exteriorPower.oneEquiv k (T → k)).symm a
    wedgeOne k (T → k) (i + 1) e (wedgeOne k (T → k) i e b) = 0 := by
  apply Subtype.ext
  simp [exteriorPower.oneEquiv_symm_apply, ExteriorAlgebra.ιMulti_apply, ← mul_assoc]

omit [Fintype T] [DecidableEq T] in
private theorem wedgeOne_swap (i : ℕ) (a a' : T → k) (b : E[i]) :
    let e := (exteriorPower.oneEquiv k (T → k)).symm a
    let e' := (exteriorPower.oneEquiv k (T → k)).symm a'
    wedgeOne k (T → k) (i + 1) e (wedgeOne k (T → k) i e' b) +
      wedgeOne k (T → k) (i + 1) e' (wedgeOne k (T → k) i e b) = 0 := by
  apply Subtype.ext
  simp [exteriorPower.oneEquiv_symm_apply, ExteriorAlgebra.ιMulti_apply, ← mul_assoc, ← add_mul]

private theorem rawD_comp (i : ℕ) (ω : Q ⊗[k] E[i]) :
    rawD k T p (i + 1) (rawD k T p i ω) = 0 := by
  induction ω using TensorProduct.inductionOn with
  | add a b ha hb => simp [ha, hb]
  | tmul f α =>
      simp only [rawD, LinearMap.sum_apply, TensorProduct.map_tmul, map_sum]
      rw [← Finset.sum_product']
      refine Finset.sum_ninvolution Prod.swap ?_ ?_ (by simp) (by simp)
      · rintro ⟨a, b⟩
        dsimp
        rw [completedPderiv_comm k T p b a, ← TensorProduct.tmul_add, wedgeOne_swap,
          TensorProduct.tmul_zero]
      · rintro ⟨a, b⟩ h
        intro he
        have hab : b = a := congrArg Prod.fst he
        subst b
        exact h (by rw [wedgeOne_sq, TensorProduct.tmul_zero])

/-- 完備形式の微分を二回作用させると零。 -/
theorem completedDeRhamD_comp (i : ℕ) (ω : completedForms k T p i) :
    completedDeRhamD k T p (i + 1) (completedDeRhamD k T p i ω) = 0 := by
  apply (completedFormsCoeffEquiv k T p (i + 1 + 1)).injective
  rw [completedFormsCoeffEquiv_d, completedFormsCoeffEquiv_d, rawD_comp, map_zero]

/-- 完備多項式環の微分形式を次数ごとに置いた de Rham 余鎖複体。 -/
def completedDeRhamComplex : CochainComplex (ModuleCat.{u} k) ℕ :=
  CochainComplex.of (fun i => ModuleCat.of k (completedForms k T p i))
    (fun i => ModuleCat.ofHom (completedDLinear k T p i))
    (fun i => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact completedDeRhamD_comp k T p i)

end SerrePositivity.DeRham
