module

public import Mathlib.RingTheory.DividedPowerAlgebra.Init
public import Mathlib.RingTheory.Derivation.Lie
public import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# 自由分冪代数の微分

## 概要
自由生成加群からの線形写像を、分冪と両立する導分に延長する。

## 方針
自明な平方零拡大に、分冪の一次の変化を加えた像を取る。

## 規約
正次数の分冪の微分では、分冪の次数を一つ下げる。

## 使われ方
pd de Rham 微分の構成。
-/

public noncomputable section

namespace SerrePositivity.BhattScholze

open DividedPowerAlgebra Finset

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

local notation "D" => DividedPowerAlgebra R M

private def dpTangent (f : M →ₗ[R] D) : ℕ → M → D
  | 0, _ => 0
  | n + 1, x => dp R n x • f x

private def dpJet (f : M →ₗ[R] D) (n : ℕ) (x : M) : TrivSqZeroExt D D :=
  (dp R n x, dpTangent f n x)

@[local simp] private theorem dpJet_fst (f : M →ₗ[R] D) (n : ℕ) (x : M) :
    (dpJet f n x).fst = dp R n x := rfl

@[local simp] private theorem dpJet_snd (f : M →ₗ[R] D) (n : ℕ) (x : M) :
    (dpJet f n x).snd = dpTangent f n x := rfl

private theorem dpJet_smul (f : M →ₗ[R] D) (n : ℕ) (r : R) (x : M) :
    dpJet f n (r • x) = r ^ n • dpJet f n x := by
  ext
  · exact dp_smul
  · rw [TrivSqZeroExt.snd_smul]
    cases n with
    | zero => simp [dpJet, dpTangent]
    | succ n =>
      simp only [dpJet, dpTangent, TrivSqZeroExt.snd_mk,
        dp_smul, map_smul, smul_assoc]
      rw [smul_comm (dp R n x) r, smul_smul, ← pow_succ]

private theorem dpJet_mul (f : M →ₗ[R] D) (n m : ℕ) (x : M) :
    dpJet f n x * dpJet f m x = (n + m).choose n • dpJet f (n + m) x := by
  ext
  · exact dp_mul
  · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_smul, dpJet_fst, dpJet_snd,
      op_smul_eq_smul]
    cases n with
    | zero => simp [dpTangent, dp_zero]
    | succ n =>
      cases m with
      | zero => simp [dpTangent, dp_zero]
      | succ m =>
        change dp R (n + 1) x • (dp R m x • f x) + dp R (m + 1) x • (dp R n x • f x) =
          (n + 1 + (m + 1)).choose (n + 1) • (dp R (n + 1 + m) x • f x)
        rw [smul_smul, smul_smul, mul_comm (dp R (m + 1) x), dp_mul, dp_mul]
        have e : n + 1 + m = n + (m + 1) := by omega
        rw [← e, ← add_smul, ← add_nsmul, add_comm ((n + 1 + m).choose (n + 1))]
        rw [← Nat.choose_succ_succ' (n + 1 + m) n]
        exact smul_assoc _ _ _

private theorem dpJet_add (f : M →ₗ[R] D) (n : ℕ) (x y : M) :
    dpJet f n (x + y) = ∑ ij ∈ antidiagonal n, dpJet f ij.1 x * dpJet f ij.2 y := by
  ext
  · simpa only [dpJet_fst, TrivSqZeroExt.fst_sum, TrivSqZeroExt.fst_mul] using
      (dp_add (R := R) (n := n) (x := x) (y := y))
  · simp only [dpJet_fst, dpJet_snd, TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_mul,
      op_smul_eq_smul, sum_add_distrib]
    cases n with
    | zero => simp [dpTangent]
    | succ n =>
      rw [Finset.Nat.sum_antidiagonal_succ', Finset.Nat.sum_antidiagonal_succ]
      simp only [dpTangent, smul_zero, zero_add, map_add, smul_add,
        dp_add (x := x) (y := y),
        sum_smul, smul_smul]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro ij _
      rw [mul_comm]

private def dpJetHom (f : M →ₗ[R] D) : D →ₐ[R] TrivSqZeroExt D D :=
  lift' (f := fun nx => dpJet f nx.1 nx.2)
    (fun x => by ext <;> simp [dpJet, dpTangent, dp_zero])
    (dpJet_smul f) (dpJet_mul f) (dpJet_add f)

private theorem dpJetHom_dp (f : M →ₗ[R] D) (n : ℕ) (x : M) :
    dpJetHom f (dp R n x) = dpJet f n x := by
  unfold dpJetHom
  rw [lift'_apply_dp]

private theorem dpJetHom_fst (f : M →ₗ[R] D) (a : D) :
    (dpJetHom f a).fst = a := by
  have h : (TrivSqZeroExt.fstHom R D D).comp (dpJetHom f) = AlgHom.id R D :=
    DividedPowerAlgebra.algHom_ext fun n x => by
      change (dpJetHom f (dp R n x)).fst = dp R n x
      rw [dpJetHom_dp]
      rfl
  exact DFunLike.congr_fun h a

/-- 自由生成加群からの線形写像を分冪導分に延長する。 -/
def freeDPDerivation (f : M →ₗ[R] D) : Derivation R D D :=
  Derivation.mk' ((TrivSqZeroExt.sndHom D D).restrictScalars R ∘ₗ (dpJetHom f).toLinearMap)
    (fun a b => by
      change (dpJetHom f (a * b)).snd = a • (dpJetHom f b).snd + b • (dpJetHom f a).snd
      rw [map_mul, TrivSqZeroExt.snd_mul, dpJetHom_fst, dpJetHom_fst, op_smul_eq_smul])

/-- 正次数の分冪では一つ下の分冪を生成元の微分に掛ける。 -/
@[simp]
theorem freeDPDerivation_dp_succ (f : M →ₗ[R] D) (n : ℕ) (x : M) :
    freeDPDerivation f (dp R (n + 1) x) = dp R n x • f x := by
  change (dpJetHom f (dp R (n + 1) x)).snd = _
  rw [dpJetHom_dp]
  rfl

private def derivationJet (d : Derivation R D D) : D →ₐ[R] TrivSqZeroExt D D where
  toFun x := (x, d x)
  map_zero' := TrivSqZeroExt.ext rfl (map_zero d)
  map_one' := TrivSqZeroExt.ext rfl d.map_one_eq_zero
  map_add' x y := TrivSqZeroExt.ext rfl (map_add d x y)
  map_mul' x y := TrivSqZeroExt.ext rfl (by
    change d (x * y) = x • d y + MulOpposite.op y • d x
    rw [op_smul_eq_smul, d.leibniz])
  commutes' r := TrivSqZeroExt.ext rfl (d.map_algebraMap r)

/-- 自由分冪代数の導分は分冪での値により決まる。 -/
theorem freeDPDerivation_ext {d e : Derivation R D D}
    (h : ∀ n x, d (dp R n x) = e (dp R n x)) : d = e := by
  have h' : derivationJet d = derivationJet e := DividedPowerAlgebra.algHom_ext fun n x =>
    TrivSqZeroExt.ext rfl (h n x)
  ext x
  exact congrArg (fun f : D →ₐ[R] TrivSqZeroExt D D => (f x).snd) h'

variable {S : Type*}

/-- 指定した自由変数についての分冪偏微分。 -/
def freeDPPartial (s : S) :
    Derivation R (DividedPowerAlgebra R (S →₀ R)) (DividedPowerAlgebra R (S →₀ R)) :=
  freeDPDerivation ((Algebra.linearMap R _).comp (Finsupp.lapply s))

/-- 分冪偏微分は、指数を一つ下げた分冪に生成加群の指定座標を掛ける。 -/
@[simp]
theorem freeDPPartial_dp_succ (s : S) (n : ℕ) (x : S →₀ R) :
    freeDPPartial s (dp R (n + 1) x) = (x s) • dp R n x := by
  rw [freeDPPartial, freeDPDerivation_dp_succ]
  change dp R n x * algebraMap R _ (x s) = (x s) • dp R n x
  rw [Algebra.smul_def, mul_comm]

/-- 自由分冪代数の偏微分は互いに可換。 -/
theorem freeDPPartial_comm (s t : S) (x : DividedPowerAlgebra R (S →₀ R)) :
    freeDPPartial s (freeDPPartial t x) = freeDPPartial t (freeDPPartial s x) := by
  have h : ⁅freeDPPartial (R := R) s, freeDPPartial (R := R) t⁆ = 0 := by
    apply freeDPDerivation_ext
    intro n a
    rw [Derivation.commutator_apply, Derivation.zero_apply]
    rcases n with _ | _ | n
    · simp [dp_zero]
    · simp [dp_zero]
    · simp only [freeDPPartial_dp_succ, Derivation.map_smul, smul_smul]
      rw [mul_comm (a s) (a t), sub_self]
  exact sub_eq_zero.mp (by
    simpa only [Derivation.commutator_apply, Derivation.zero_apply] using
      congrArg (fun d : Derivation R (DividedPowerAlgebra R (S →₀ R)) _ => d x) h)

end SerrePositivity.BhattScholze
