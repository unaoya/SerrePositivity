module

public import SerrePositivity.CommutativeAlgebra.Adic.Principal
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # 主元を反転する局所化の自由telescope

自由加群E=⊕ₙRの写像eₙ ↦ eₙ-feₙ₊₁と、eₙ ↦ f⁻ⁿによる局所化への写像。
その双対を列の差分作用へ同定する。導来圏への移送は別工程である。
-/

@[expose] public noncomputable section
namespace SerrePositivity
open scoped Pointwise
variable (R : Type*) [CommRing R]

/-- 主元を反転する自由telescopeの各項。 -/
abbrev LocalizationTelescopeFree := ℕ →₀ R

/-- 自由telescopeの差分写像。 -/
def localizationTelescopeMap (f : R) :
    LocalizationTelescopeFree R →ₗ[R] LocalizationTelescopeFree R :=
  LinearMap.id - f • Finsupp.lmapDomain R R Nat.succ

@[simp] theorem localizationTelescopeMap_single (f r : R) (n : ℕ) :
    localizationTelescopeMap R f (Finsupp.single n r) =
      Finsupp.single n r - Finsupp.single (n + 1) (f * r) := by
  simp [localizationTelescopeMap, Finsupp.lmapDomain_apply, Finsupp.smul_single, smul_eq_mul]

@[simp] theorem localizationTelescopeMap_apply_zero (f : R) (x : LocalizationTelescopeFree R) :
    localizationTelescopeMap R f x 0 = x 0 := by
  have h0 : Finsupp.mapDomain Nat.succ x 0 = 0 :=
    Finsupp.mapDomain_of_notMem_range (f := Nat.succ) x 0 (by simp)
  simp [localizationTelescopeMap, Finsupp.lmapDomain_apply, h0]

@[simp] theorem localizationTelescopeMap_apply_succ (f : R) (x : LocalizationTelescopeFree R)
    (n : ℕ) : localizationTelescopeMap R f x (n + 1) = x (n + 1) - f * x n := by
  simp [localizationTelescopeMap, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_apply_of_injective Nat.succ_injective, smul_eq_mul]

/-- telescopeの最初の写像は、fが零因子であっても単射。 -/
theorem localizationTelescopeMap_injective (f : R) :
    Function.Injective (localizationTelescopeMap R f) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro x hx
  have hh := LinearMap.mem_ker.mp hx
  have hzero (n : ℕ) : x n = 0 := by
    induction n with
    | zero => simpa using congrArg (fun z : ℕ →₀ R ↦ z 0) hh
    | succ n hn =>
      have h := congrArg (fun z : ℕ →₀ R ↦ z (n + 1)) hh
      simpa [hn] using h
  exact Finsupp.ext hzero

/-- eₙをf⁻ⁿへ送る局所化への線形写像。 -/
def localizationTelescopeToAway (f : R) : LocalizationTelescopeFree R →ₗ[R] Localization.Away f :=
  Finsupp.linearCombination R (fun n ↦ (IsLocalization.Away.invSelf f : Localization.Away f) ^ n)

@[simp] theorem localizationTelescopeToAway_single (f r : R) (n : ℕ) :
    localizationTelescopeToAway R f (Finsupp.single n r) =
      algebraMap R (Localization.Away f) r * IsLocalization.Away.invSelf f ^ n := by
  simp [localizationTelescopeToAway, Algebra.smul_def]

/-- 局所化への写像は全射。 -/
theorem localizationTelescopeToAway_surjective (f : R) :
    Function.Surjective (localizationTelescopeToAway R f) := by
  intro z
  obtain ⟨n, r, hr⟩ := IsLocalization.Away.surj f z
  refine ⟨Finsupp.single n r, ?_⟩
  rw [localizationTelescopeToAway_single, ← hr, mul_assoc, ← mul_pow,
    IsLocalization.Away.mul_invSelf, one_pow, mul_one]

/-- 自由加群からの線形写像は、基底上の値の列で一意に決まる。 -/
def localizationTelescopeHomEquiv (M : Type*) [AddCommGroup M] [Module R M] :
    (LocalizationTelescopeFree R →ₗ[R] M) ≃ₗ[R] (ℕ → M) where
  toFun g n := g (Finsupp.single n 1)
  invFun x := Finsupp.linearCombination R x
  left_inv g := by
    apply Finsupp.lhom_ext
    intro n r
    have hs : Finsupp.single n r = r • Finsupp.single n (1 : R) := by simp
    change (Finsupp.linearCombination R (fun i ↦ g (Finsupp.single i 1)))
      (Finsupp.single n r) = g (Finsupp.single n r)
    rw [Finsupp.linearCombination_single, hs, g.map_smul]
  right_inv x := by ext n; simp
  map_add' g h := by ext n; rfl
  map_smul' r g := by ext n; rfl

/-- telescopeの写像の双対は、前回証明した列の差分作用である。 -/
theorem localizationTelescopeHomEquiv_comp (f : R) (M : Type*) [AddCommGroup M] [Module R M]
    (g : LocalizationTelescopeFree R →ₗ[R] M) :
    localizationTelescopeHomEquiv R M (g.comp (localizationTelescopeMap R f)) =
      adicRecurrenceMap f (localizationTelescopeHomEquiv R M g) := by
  ext n
  change g (localizationTelescopeMap R f (Finsupp.single n 1)) = _
  rw [localizationTelescopeMap_single]
  have hs : Finsupp.single (n + 1) (f * 1) = f • Finsupp.single (n + 1) (1 : R) := by simp
  rw [hs, map_sub, map_smul]
  rfl

/-- 局所化で逆元の冪は、fを掛けると一段戻る。 -/
theorem localizationTelescope_inv_step (f : R) (n : ℕ) :
    algebraMap R (Localization.Away f) f * IsLocalization.Away.invSelf f ^ (n + 1) =
      IsLocalization.Away.invSelf f ^ n := by
  rw [pow_succ]
  calc
    _ = (algebraMap R (Localization.Away f) f * IsLocalization.Away.invSelf f) *
        IsLocalization.Away.invSelf f ^ n := by ring
    _ = _ := by rw [IsLocalization.Away.mul_invSelf, one_mul]

/-- 二つのtelescope写像の合成は零。 -/
theorem localizationTelescope_comp_eq_zero (f : R) :
    (localizationTelescopeToAway R f).comp (localizationTelescopeMap R f) = 0 := by
  apply Finsupp.lhom_ext
  intro n r
  simp only [LinearMap.comp_apply, localizationTelescopeMap_single, map_sub,
    localizationTelescopeToAway_single, map_mul, LinearMap.zero_apply]
  rw [mul_comm (algebraMap R (Localization.Away f) f), mul_assoc,
    localizationTelescope_inv_step, sub_self]

/-- 基底を先の段へ移す有限個の関係は、telescope写像の像に入る。 -/
theorem localizationTelescope_single_relation (f r : R) (n k : ℕ) :
    Finsupp.single n r - Finsupp.single (n + k) (f ^ k * r) ∈
      (localizationTelescopeMap R f).range := by
  induction k with
  | zero => simp
  | succ k hk =>
    have hnext : Finsupp.single (n + k) (f ^ k * r) -
        Finsupp.single (n + k + 1) (f ^ (k + 1) * r) ∈
          (localizationTelescopeMap R f).range := by
      refine ⟨Finsupp.single (n + k) (f ^ k * r), ?_⟩
      rw [localizationTelescopeMap_single]
      congr 2
      ring
    have hh := (localizationTelescopeMap R f).range.add_mem hk hnext
    simpa only [Nat.add_assoc, sub_add_sub_cancel] using hh

/-- 局所化への写像の核は、telescope写像の像に一致する。 -/
theorem localizationTelescope_range_eq_ker (f : R) :
    (localizationTelescopeMap R f).range = (localizationTelescopeToAway R f).ker := by
  classical
  have hle : (localizationTelescopeMap R f).range ≤
      (localizationTelescopeToAway R f).ker :=
    LinearMap.range_le_ker_iff.mpr (localizationTelescope_comp_eq_zero R f)
  apply le_antisymm hle
  intro x hx
  let N := x.support.sup id
  let P := x.sum (fun n r ↦ f ^ (N - n) * r)
  let q := (localizationTelescopeMap R f).range.mkQ
  have hrel (n : ℕ) (hn : n ∈ x.support) :
      q (Finsupp.single n (x n)) = q (Finsupp.single N (f ^ (N - n) * x n)) := by
    apply (Submodule.Quotient.eq _).mpr
    have hbound : n ≤ N := Finset.le_sup (f := id) hn
    simpa only [Nat.add_sub_of_le hbound] using
      localizationTelescope_single_relation R f (x n) n (N - n)
  have hqx : q x = q (Finsupp.single N P) := by
    calc
      q x = ∑ n ∈ x.support, q (Finsupp.single n (x n)) := by
        conv_lhs => rw [← x.sum_single]
        simp only [Finsupp.sum, map_sum]
      _ = ∑ n ∈ x.support, q (Finsupp.single N (f ^ (N - n) * x n)) := by
        apply Finset.sum_congr rfl
        exact hrel
      _ = q (Finsupp.single N P) := by
        dsimp only [P]
        rw [Finsupp.single_sum]
        simp only [Finsupp.sum, map_sum]
  let e := (localizationTelescopeMap R f).range.liftQ (localizationTelescopeToAway R f) hle
  have h := congrArg e hqx
  change localizationTelescopeToAway R f x =
    localizationTelescopeToAway R f (Finsupp.single N P) at h
  have hzero : localizationTelescopeToAway R f (Finsupp.single N P) = 0 :=
    h.symm.trans (LinearMap.mem_ker.mp hx)
  rw [localizationTelescopeToAway_single] at hzero
  have hP : algebraMap R (Localization.Away f) P = 0 := by
    have hh := congrArg (fun z : Localization.Away f ↦
      z * algebraMap R (Localization.Away f) f ^ N) hzero
    rw [mul_assoc, ← mul_pow, mul_comm (IsLocalization.Away.invSelf f),
      IsLocalization.Away.mul_invSelf, one_pow, mul_one, zero_mul] at hh
    exact hh
  obtain ⟨k, hk⟩ := IsLocalization.Away.exists_of_eq f (hP.trans (map_zero _).symm)
  have hs : Finsupp.single N P ∈ (localizationTelescopeMap R f).range := by
    have hh := localizationTelescope_single_relation R f P N k
    simpa only [mul_zero, hk, Finsupp.single_zero, sub_zero] using hh
  have hqzero : q x = 0 := hqx.trans ((Submodule.Quotient.mk_eq_zero _).mpr hs)
  exact (Submodule.Quotient.mk_eq_zero _).mp hqzero

end SerrePositivity
