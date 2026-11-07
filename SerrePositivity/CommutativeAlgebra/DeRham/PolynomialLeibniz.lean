module

public import SerrePositivity.CommutativeAlgebra.DeRham.Polynomial

/-!
# 多項式 de Rham 微分の Leibniz 則

## 概要
多項式形式の外積を de Rham 微分で微分する。

## 方針
純テンソルに帰着し、偏微分の積の公式と外冪の反交換性を使う。

## 規約
微分形式を左から外積する。右の因子を微分する項には左の次数の符号を付ける。

## 使われ方
de Rham コホモロジーの外積と、dg 代数としての普遍性。
-/

public section
noncomputable section

universe u

open scoped TensorProduct

namespace SerrePositivity.DeRham

variable (k : Type u) [CommRing k]

section Exterior
variable (M : Type u) [AddCommGroup M] [Module k M]

private theorem exteriorCast_coe {i j : ℕ} (h : i = j) (b : ⋀[k]^i M) :
    ((cast (congrArg (fun n => ↥(⋀[k]^n M)) h) b : ⋀[k]^j M) : ExteriorAlgebra k M) = b := by
  subst j
  rfl

private theorem wedgeOne_mul_left {i j : ℕ} (a : ⋀[k]^1 M) (b : ⋀[k]^i M) (c : ⋀[k]^j M) :
    wedgeOne k M (i + j) a (exteriorWedge k M i j b c) =
      cast (congrArg (fun n => ↥(⋀[k]^n M)) (by omega : (i + 1) + j = (i + j) + 1))
        (exteriorWedge k M (i + 1) j (wedgeOne k M i a b) c) := by
  apply Subtype.ext
  rw [exteriorCast_coe k M (by omega : (i + 1) + j = (i + j) + 1), wedgeOne_coe]
  change a.1 * (b.1 * c.1) = (wedgeOne k M i a b).1 * c.1
  rw [wedgeOne_coe, mul_assoc]

private theorem exterior_anticomm {i : ℕ} (a : M) (b : ⋀[k]^i M) :
    ExteriorAlgebra.ι k a * b.1 = (-1 : ℤ)^i • (b.1 * ExteriorAlgebra.ι k a) := by
  have hb : b ∈ Submodule.span k (Set.range (exteriorPower.ιMulti k i (M := M))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hb using Submodule.span_induction with
  | mem b hb =>
      obtain ⟨v, rfl⟩ := hb
      change ExteriorAlgebra.ι k a * ExteriorAlgebra.ιMulti k i v =
        (-1 : ℤ)^i • (ExteriorAlgebra.ιMulti k i v * ExteriorAlgebra.ι k a)
      simpa [Units.smul_def, Units.val_pow_eq_pow_val] using
        ExteriorAlgebra.ι_mul_ιMulti_anticomm (R := k) a v
  | zero => simp
  | add b c _ _ hb hc =>
      change ExteriorAlgebra.ι k a * (b.1 + c.1) =
        (-1 : ℤ)^i • ((b.1 + c.1) * ExteriorAlgebra.ι k a)
      rw [mul_add, add_mul, smul_add, hb, hc]
  | smul r b _ hb =>
      change ExteriorAlgebra.ι k a * (r • b.1) =
        (-1 : ℤ)^i • ((r • b.1) * ExteriorAlgebra.ι k a)
      rw [Algebra.mul_smul_comm, smul_mul_assoc, smul_comm, hb]

private theorem wedgeOne_mul_right {i j : ℕ} (a : M) (b : ⋀[k]^i M) (c : ⋀[k]^j M) :
    let e := (exteriorPower.oneEquiv k M).symm a
    wedgeOne k M (i + j) e (exteriorWedge k M i j b c) =
      (-1 : ℤ)^i • exteriorWedge k M i (j + 1) b (wedgeOne k M j e c) := by
  intro e
  apply Subtype.ext
  rw [wedgeOne_coe]
  change e.1 * (b.1 * c.1) = (-1 : ℤ)^i • (b.1 * (wedgeOne k M j e c).1)
  rw [wedgeOne_coe]
  have he : e.1 = ExteriorAlgebra.ι k a := by
    simp [e, exteriorPower.oneEquiv_symm_apply, ExteriorAlgebra.ιMulti_apply]
  rw [he, ← mul_assoc, exterior_anticomm, smul_mul_assoc, mul_assoc]

end Exterior

variable (T : Type u) [Fintype T] [DecidableEq T]

local notation "E[" n "]" => (⋀[k]^n (T → k))
local notation "P" => Poly k T

private theorem formsCast_add {i j : ℕ} (h : i = j) (a b : forms k T i) :
    cast (congrArg (forms k T) h) (a + b) =
      cast (congrArg (forms k T) h) a + cast (congrArg (forms k T) h) b := by
  subst j
  rfl

private theorem formsCast_sum {ι : Type*} {i j : ℕ} (h : i = j) (s : Finset ι)
    (f : ι → forms k T i) :
    cast (congrArg (forms k T) h) (∑ a ∈ s, f a) =
      ∑ a ∈ s, cast (congrArg (forms k T) h) (f a) := by
  subst j
  rfl

private theorem formsCast_tmul {i j : ℕ} (h : i = j) (f : P) (b : E[i]) :
    cast (congrArg (forms k T) h) (f ⊗ₜ[k] b) =
      f ⊗ₜ[k] cast (congrArg (fun n => ↥(E[n])) h) b := by
  subst j
  rfl

private theorem wedge_tmul {i j : ℕ} (f g : P) (b : E[i]) (c : E[j]) :
    wedge k T (f ⊗ₜ[k] b) (g ⊗ₜ[k] c) =
      (f * g) ⊗ₜ[k] exteriorWedge k (T → k) i j b c := by
  rw [wedge, TensorProduct.map₂_apply_tmul, TensorProduct.map_tmul]
  rfl

/-- 概要：多項式の de Rham 微分は外積について符号付き Leibniz 則を満たす。
方針：偏微分の積の公式と外冪の反交換性を純テンソルに適用する。
規約：右因子を微分する項の符号は左因子の次数で決める。
使われ方：de Rham 複体の積と dg 代数の普遍性。 -/
theorem deRhamD_wedge {i j : ℕ} (ω : forms k T i) (η : forms k T j) :
    deRhamD k T (i + j) (wedge k T ω η) =
      cast (congrArg (forms k T) (by omega : (i + 1) + j = (i + j) + 1))
        (wedge k T (deRhamD k T i ω) η) +
      (-1 : ℤ)^i • wedge k T ω (deRhamD k T j η) := by
  let e : (i + 1) + j = (i + j) + 1 := by omega
  induction ω using TensorProduct.inductionOn with
  | add a b ha hb =>
      simp only [wedge, map_add, LinearMap.add_apply, smul_add] at ha hb ⊢
      rw [formsCast_add k T e, ha, hb]
      ac_rfl
  | tmul f b =>
      induction η using TensorProduct.inductionOn with
      | add c d hc hd =>
          simp only [wedge, map_add, smul_add] at hc hd ⊢
          rw [formsCast_add k T e, hc, hd]
          ac_rfl
      | tmul g c =>
          let v (t : T) := (exteriorPower.oneEquiv k (T → k)).symm (Pi.single t 1)
          simp only [wedge_tmul, deRhamD, deRhamDLinear, LinearMap.toAddMonoidHom_coe,
            LinearMap.sum_apply, TensorProduct.map_tmul]
          simp only [wedge, map_sum, LinearMap.sum_apply, TensorProduct.map₂_apply_tmul,
            TensorProduct.map_tmul]
          rw [formsCast_sum k T e, Finset.smul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro t _
          let w := wedgeOne k (T → k) (i + j) (v t) (exteriorWedge k (T → k) i j b c)
          let l := exteriorWedge k (T → k) (i + 1) j (wedgeOne k (T → k) i (v t) b) c
          let r := exteriorWedge k (T → k) i (j + 1) b (wedgeOne k (T → k) j (v t) c)
          change (MvPolynomial.pderiv t (f * g)) ⊗ₜ[k] w =
            cast (congrArg (forms k T) e) ((MvPolynomial.pderiv t f * g) ⊗ₜ[k] l) +
              (-1 : ℤ)^i • ((f * MvPolynomial.pderiv t g) ⊗ₜ[k] r)
          have hprod : MvPolynomial.pderiv t (f * g) =
              MvPolynomial.pderiv t f * g + f * MvPolynomial.pderiv t g := by
            rw [MvPolynomial.pderiv_mul]
          rw [hprod, TensorProduct.add_tmul, formsCast_tmul k T e,
            ← TensorProduct.tmul_smul]
          congr 1
          · exact congrArg (fun x : E[i + j + 1] => (MvPolynomial.pderiv t f * g) ⊗ₜ[k] x)
              (wedgeOne_mul_left k (T → k) (v t) b c)
          · exact congrArg (fun x : E[i + j + 1] => (f * MvPolynomial.pderiv t g) ⊗ₜ[k] x)
              (wedgeOne_mul_right k (T → k) (Pi.single t 1) b c)

end SerrePositivity.DeRham
