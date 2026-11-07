module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.RingTheory.Derivation.Lie
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# 多項式代数の微分形式

## 概要
有限変数の多項式代数の微分形式を外冪で表し、外積と多項式の de Rham 微分を定める。

## 方針
変数で添字付けた自由加群の外冪を多項式代数に係数拡大し、微分は偏微分と外積の和で与える。

## 規約
外積で新しい微分を左に置く。微分は基底環上の線形写像。

## 使われ方
Hodge–Tate 写像の定義と、多項式代数の Cartier 同型。
-/

@[expose] public section
noncomputable section

universe u

open scoped TensorProduct

namespace SerrePositivity.DeRham

/-- 多項式形式の係数環。 -/
abbrev Poly (k : Type u) [CommRing k] (T : Type u) := MvPolynomial T k

/-- 概要：多項式代数の i 次微分形式。
方針：変数で添字付けた自由加群の外冪を係数拡大する。
規約：自由加群は関数の加群で表す。
使われ方：外積と de Rham 微分の項。 -/
abbrev forms (k : Type u) [CommRing k] (T : Type u) [Fintype T] [DecidableEq T] (i : ℕ) : Type u :=
  Poly k T ⊗[k] (⋀[k]^i (T → k))

variable (k : Type u) [CommRing k] (T : Type u) [Fintype T] [DecidableEq T]

/-- 概要：変数に対応する 1 次微分形式。
方針：標準ベクトルを第 1 外冪に移し、係数 1 を掛ける。
規約：変数 t のベクトルは t で 1、それ以外で 0。
使われ方：Hodge–Tate 写像と Cartier の生成元。 -/
def dX (t : T) : forms k T 1 :=
  1 ⊗ₜ[k] (exteriorPower.oneEquiv (R := k) (M := T → k)).symm (Pi.single t 1)

/-- 概要：次数 0 の微分形式と係数環との同一視。
方針：第 0 外冪を基底環と同定し、テンソル積の右単位同型を用いる。
規約：多項式から形式への向き。
使われ方：次数 0 の生成元と de Rham 微分。 -/
def formsZeroEquiv : Poly k T ≃ₗ[k] forms k T 0 :=
  (TensorProduct.rid k (Poly k T)).symm.trans
    (TensorProduct.congr (LinearEquiv.refl k (Poly k T)) (exteriorPower.zeroEquiv k (T → k)).symm)

/-- 外冪の斉次元の積を外冪の次数ごとの双線形写像として読む。 -/
def exteriorWedge (M : Type u) [AddCommGroup M] [Module k M] (i j : ℕ) :
    (⋀[k]^i M) →ₗ[k] (⋀[k]^j M) →ₗ[k] (⋀[k]^(i + j) M) where
  toFun a :=
    { toFun := fun b => ⟨a.1 * b.1, SetLike.mul_mem_graded a.2 b.2⟩
      map_add' := fun b c => Subtype.ext (mul_add a.1 b.1 c.1)
      map_smul' := fun r b => Subtype.ext (Algebra.mul_smul_comm r a.1 b.1) }
  map_add' a b := LinearMap.ext fun c => Subtype.ext (add_mul a.1 b.1 c.1)
  map_smul' r a := LinearMap.ext fun b => Subtype.ext (smul_mul_assoc r a.1 b.1)

/-- 概要：多項式形式の外積。
方針：係数の積と斉次外冪の積をテンソルする。
規約：因子の順序を保つ。
使われ方：多項式 de Rham 複体の積。 -/
def wedge {i j : ℕ} (a : forms k T i) (b : forms k T j) : forms k T (i + j) :=
  TensorProduct.map₂ (LinearMap.mul k (Poly k T)) (exteriorWedge k (T → k) i j) a b

/-- 第 1 外冪の元を左から掛け、次数を i + 1 の形で表す。 -/
def wedgeOne (M : Type u) [AddCommGroup M] [Module k M] (i : ℕ)
    (a : ⋀[k]^1 M) : (⋀[k]^i M) →ₗ[k] (⋀[k]^(i + 1) M) :=
  (LinearEquiv.ofEq _ _ (congrArg (fun n => ⋀[k]^n M) (Nat.add_comm 1 i))).toLinearMap.comp
    (exteriorWedge k M 1 i a)

/-- 偏微分と外積の和としての係数環上の線形写像。 -/
def deRhamDLinear (i : ℕ) :
    forms k T i →ₗ[k] forms k T (i + 1) :=
  ∑ t : T, TensorProduct.map (MvPolynomial.pderiv t).toLinearMap
    (wedgeOne k (T → k) i
      ((exteriorPower.oneEquiv (R := k) (M := T → k)).symm (Pi.single t 1)))

/-- 概要：多項式形式の de Rham 微分。
方針：各変数で係数を偏微分し、対応する 1 次形式を左から外積する。
規約：係数環上の線形写像の加法写像としての表示。
使われ方：多項式 de Rham 複体。 -/
def deRhamD (i : ℕ) : forms k T i →+ forms k T (i + 1) :=
  (deRhamDLinear k T i).toAddMonoidHom

@[simp]
theorem wedgeOne_coe (M : Type u) [AddCommGroup M] [Module k M] (i : ℕ)
    (a : ⋀[k]^1 M) (b : ⋀[k]^i M) :
    (wedgeOne k M i a b : ExteriorAlgebra k M) = a.1 * b.1 :=
  rfl

omit [Fintype T] [DecidableEq T] in
private theorem pderiv_comm (a b : T) (f : Poly k T) :
    MvPolynomial.pderiv a (MvPolynomial.pderiv b f) =
      MvPolynomial.pderiv b (MvPolynomial.pderiv a f) := by
  classical
  have h : ⁅MvPolynomial.pderiv (R := k) a, MvPolynomial.pderiv (R := k) b⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro t
    simp only [Derivation.commutator_apply, MvPolynomial.pderiv_X, Pi.single_apply]
    split <;> split <;> simp
  exact sub_eq_zero.mp (by
    simpa only [Derivation.commutator_apply, Derivation.zero_apply] using
      congrArg (fun D : Derivation k (Poly k T) (Poly k T) => D f) h)

private theorem wedgeOne_sq (M : Type u) [AddCommGroup M] [Module k M] (i : ℕ)
    (a : M) (b : ⋀[k]^i M) :
    let e := (exteriorPower.oneEquiv k M).symm a
    wedgeOne k M (i + 1) e (wedgeOne k M i e b) = 0 := by
  apply Subtype.ext
  simp [exteriorPower.oneEquiv_symm_apply, ExteriorAlgebra.ιMulti_apply, ← mul_assoc]

private theorem wedgeOne_swap (M : Type u) [AddCommGroup M] [Module k M] (i : ℕ)
    (a a' : M) (b : ⋀[k]^i M) :
    let e := (exteriorPower.oneEquiv k M).symm a
    let e' := (exteriorPower.oneEquiv k M).symm a'
    wedgeOne k M (i + 1) e (wedgeOne k M i e' b) +
      wedgeOne k M (i + 1) e' (wedgeOne k M i e b) = 0 := by
  apply Subtype.ext
  simp [exteriorPower.oneEquiv_symm_apply, ExteriorAlgebra.ιMulti_apply, ← mul_assoc, ← add_mul]

/-- 概要：多項式の de Rham 微分を二回作用させると零。
方針：偏微分の可換性と外積の反交換性で添字を交換した項を打ち消す。
規約：対角項は第 1 外冪の元の平方零による。
使われ方：de Rham 余鎖複体。 -/
theorem deRhamD_comp (i : ℕ) (ω : forms k T i) :
    deRhamD k T (i + 1) (deRhamD k T i ω) = 0 := by
  induction ω using TensorProduct.inductionOn with
  | add a b ha hb => simp [ha, hb]
  | tmul f α =>
    simp only [deRhamD, deRhamDLinear, LinearMap.toAddMonoidHom_coe, LinearMap.sum_apply,
      TensorProduct.map_tmul, map_sum]
    rw [← Finset.sum_product']
    refine Finset.sum_ninvolution Prod.swap ?_ ?_ (by simp) (by simp)
    · rintro ⟨a, b⟩
      dsimp
      rw [pderiv_comm k T b a, ← TensorProduct.tmul_add, wedgeOne_swap, TensorProduct.tmul_zero]
    · rintro ⟨a, b⟩ h
      intro he
      have hab : b = a := congrArg Prod.fst he
      subst b
      exact h (by rw [wedgeOne_sq, TensorProduct.tmul_zero])

/-- 概要：多項式代数の de Rham 余鎖複体。
方針：各次数に多項式微分形式を置き、偏微分の和を微分にする。
規約：係数環上の加群の余鎖複体。
使われ方：de Rham コホモロジーと Cartier 同型。 -/
def deRhamComplex : CochainComplex (ModuleCat.{u} k) ℕ :=
  CochainComplex.of (fun i => ModuleCat.of k (forms k T i))
    (fun i => ModuleCat.ofHom (deRhamDLinear k T i))
    (fun i => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact deRhamD_comp k T i x)

end SerrePositivity.DeRham
