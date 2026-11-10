module

public import SerrePositivity.CommutativeAlgebra.DeRham.Polynomial
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-!
# 外冪の内部積

## 概要
線形汎関数による Clifford の収縮を外冪の斉次成分に制限する。

## 方針
生成元を左から掛けた積での公式を使い、収縮が次数を一つ下げることを示す。

## 規約
左収縮を使う。

## 使われ方
分冪 Poincaré 補題の余鎖ホモトピー。
-/

public noncomputable section

universe u

namespace SerrePositivity.DeRham

variable (k M : Type u) [CommRing k] [AddCommGroup M] [Module k M]

private abbrev contraction (d : Module.Dual k M) :
    ExteriorAlgebra k M →ₗ[k] ExteriorAlgebra k M :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm k M)) d

private theorem exterior_ι_mem (a : M) :
    ExteriorAlgebra.ι k a ∈ ⋀[k]^1 M := by
  rw [← show ExteriorAlgebra.ιMulti k 1 (fun _ => a) = ExteriorAlgebra.ι k a by
    simp [ExteriorAlgebra.ιMulti_apply]]
  exact (exteriorPower.ιMulti k 1 (fun _ => a)).2

private theorem contraction_mem (d : Module.Dual k M) (n : ℕ) (x : ExteriorAlgebra k M)
    (hx : x ∈ ⋀[k]^n M) : contraction k M d x ∈ ⋀[k]^(n-1) M := by
  induction n generalizing x with
  | zero =>
    rw [← exteriorPower.ιMulti_span_fixedDegree] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      simp [contraction, ExteriorAlgebra.ιMulti_apply, CliffordAlgebra.contractLeft_one]
    | zero => simp
    | add y z _ _ hy hz => simpa only [map_add] using Submodule.add_mem _ hy hz
    | smul a y _ hy => simpa only [map_smul] using Submodule.smul_mem _ a hy
  | succ n ih =>
    rw [← exteriorPower.ιMulti_span_fixedDegree k (n+1) M] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      rw [ExteriorAlgebra.ιMulti_succ_apply]
      change (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm k M)) d)
        (ExteriorAlgebra.ι k (v 0) * ExteriorAlgebra.ιMulti k n (Matrix.vecTail v)) ∈ _
      rw [CliffordAlgebra.contractLeft_ι_mul]
      have ht : ExteriorAlgebra.ιMulti k n (Matrix.vecTail v) ∈ ⋀[k]^n M :=
        (exteriorPower.ιMulti k n (Matrix.vecTail v)).2
      apply Submodule.sub_mem _ (Submodule.smul_mem _ _ ht)
      cases n with
      | zero =>
        simp [ExteriorAlgebra.ιMulti_apply, CliffordAlgebra.contractLeft_one]
      | succ n =>
        have h := SetLike.mul_mem_graded (exterior_ι_mem k M (v 0)) (ih _ ht)
        simpa [contraction, Nat.add_comm] using h
    | zero => simp
    | add y z _ _ hy hz => simpa only [map_add] using Submodule.add_mem _ hy hz
    | smul a y _ hy => simpa only [map_smul] using Submodule.smul_mem _ a hy

/-- 左収縮は正次数の外冪を一つ下の外冪へ送る。 -/
def exteriorContract (d : Module.Dual k M) (n : ℕ) :
    (⋀[k]^(n+1) M) →ₗ[k] (⋀[k]^n M) :=
  ((contraction k M d).comp (Submodule.subtype _)).codRestrict _
    (fun x => contraction_mem k M d (n+1) x x.2)

/-- 斉次外冪の収縮を外代数の元として読む。 -/
theorem exteriorContract_coe (d : Module.Dual k M) (n : ℕ) (x : ⋀[k]^(n+1) M) :
    (exteriorContract k M d n x : ExteriorAlgebra k M) = CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm k M)) d x := by
  unfold exteriorContract
  rfl

/-- 一次元を左に外積してから収縮する公式。 -/
theorem exteriorContract_wedgeOne (d : Module.Dual k M) (n : ℕ) (a : M)
    (x : ⋀[k]^(n+1) M) :
    let e := (exteriorPower.oneEquiv k M).symm a
    exteriorContract k M d (n+1) (wedgeOne k M (n+1) e x) =
      d a • x - wedgeOne k M n e (exteriorContract k M d n x) := by
  intro e
  apply Subtype.ext
  simp only [exteriorContract_coe, wedgeOne_coe, e, exteriorPower.oneEquiv_symm_apply,
    exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
    mul_one, Submodule.coe_sub, Submodule.coe_smul]
  exact CliffordAlgebra.contractLeft_ι_mul (Q := (0 : QuadraticForm k M)) _ _ _

end SerrePositivity.DeRham
