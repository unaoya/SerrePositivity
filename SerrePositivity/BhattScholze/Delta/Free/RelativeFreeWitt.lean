module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeFiniteDelta
public import Mathlib.Logic.Function.Iterate
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaWitt
public import Mathlib.Algebra.MvPolynomial.Supported
public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeDelta

/-!
# 相対自由 δ 環の Witt 座標（BS 著者版 Remark 2.13・Remark 2.14 の相対版）

## 概要
Frobenius 反復の最高線形項、生成元の第 n Witt 係数（Joyal の δ_n）＝ x_(s,n) ＋ 下位の多項式という三角形表示、
x_(s,n) ↦ δ_n(x_s) による代数自己同型とその有限段版、係数の自然性、任意の元の δ jet と Witt jet の比較。

## 方針
全段の ghost 再帰式から下位変数への所属を強帰納で示し、逆変数を段数の強帰納で作る。

## 規約
基底の p 正則性を仮定する。

## 使われ方
André の一段の拡大で、d で割る包の関係式を Witt 座標のモニック方程式に移す計算（Division/Relations）。
-/

@[expose] public noncomputable section
universe u v

/-! ## 自由初期変数のFrobenius反復の正確な最高線形項

下位部分は有限Frobenius計算で再帰的に構成する。
-/

section RelativeFreeFrobeniusTopLinear

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- φ^(n+1)(X₀)から最高線形項を除いた、第n段までの具体的な多項式。 -/
def relativeFreeFrobeniusLowerPolynomial (D : DeltaStructure p A) (s : σ) :
    (n : ℕ) → MvPolynomial (σ × Fin (n + 1)) A
  | 0 => MvPolynomial.X (s, 0) ^ p
  | n + 1 => (p : MvPolynomial (σ × Fin (n + 2)) A) ^ (n + 1) *
      MvPolynomial.X (s, Fin.last (n + 1)) ^ p +
        relativeFreeFiniteFrobeniusStep n σ D (relativeFreeFrobeniusLowerPolynomial D s n)

/-- 最初の下位多項式は初期変数のp乗。 -/
@[simp] theorem relativeFreeFrobeniusLowerPolynomial_zero (D : DeltaStructure p A) (s : σ) :
    relativeFreeFrobeniusLowerPolynomial D s 0 = MvPolynomial.X (s, 0) ^ p := rfl

/-- 次の下位多項式は最高変数のp乗と、前の下位部分の有限Frobenius像。 -/
@[simp] theorem relativeFreeFrobeniusLowerPolynomial_succ
    (D : DeltaStructure p A) (s : σ) (n : ℕ) :
    relativeFreeFrobeniusLowerPolynomial D s (n + 1) =
      (p : MvPolynomial (σ × Fin (n + 2)) A) ^ (n + 1) *
        MvPolynomial.X (s, Fin.last (n + 1)) ^ p +
          relativeFreeFiniteFrobeniusStep n σ D (relativeFreeFrobeniusLowerPolynomial D s n) := rfl

/-- 全深さの自由Frobenius反復の最高変数は、p^(n+1)係数で正確に線形に現れる。 -/
theorem relativeFreeFrobenius_iterate_top_linear (D : DeltaStructure p A) (s : σ) (n : ℕ) :
    (relativeFreeDeltaStructure σ D).frobeniusLift^[n + 1] (MvPolynomial.X (s, 0)) =
      (p : RelativeFreeDeltaRing (R := A) σ) ^ (n + 1) * MvPolynomial.X (s, n + 1) +
        relativeFreeFiniteInitialPolynomialMap (n + 1) σ A
          (relativeFreeFrobeniusLowerPolynomial D s n) := by
  induction n with
  | zero =>
      rw [Function.iterate_one, DeltaStructure.frobeniusLift_apply,
        relativeFreeDeltaStructure_delta_X]
      simp [relativeFreeFrobeniusLowerPolynomial, relativeFreeFiniteInitialPolynomialMap,
        add_comm]
  | succ n ih =>
      rw [Function.iterate_succ_apply' _ (n + 1), ih, map_add, map_mul, map_pow, map_natCast,
        DeltaStructure.frobeniusLift_apply, relativeFreeDeltaStructure_delta_X,
        ← relativeFreeFiniteFrobeniusStep_image n σ D,
        relativeFreeFrobeniusLowerPolynomial_succ, map_add, map_mul, map_pow, map_natCast]
      simp only [relativeFreeFiniteInitialPolynomialMap, MvPolynomial.rename_X,
        Fin.val_last, map_pow]
      rw [pow_succ]
      ring

/-- 自由初期変数のφ^n像を初期n+1段に置く、具体的な有限多項式。 -/
def relativeFreeFrobeniusFinitePolynomial (D : DeltaStructure p A) (s : σ) :
    (n : ℕ) → MvPolynomial (σ × Fin (n + 1)) A
  | 0 => MvPolynomial.X (s, 0)
  | n + 1 => (p : MvPolynomial (σ × Fin (n + 2)) A) ^ (n + 1) *
      MvPolynomial.X (s, Fin.last (n + 1)) +
        relativeFreeFiniteStepInclusion n σ (relativeFreeFrobeniusLowerPolynomial D s n)

/-- 有限Frobenius多項式の包含像は、実際のφ反復の像。 -/
theorem relativeFreeFrobeniusFinitePolynomial_image (D : DeltaStructure p A) (s : σ) (n : ℕ) :
    relativeFreeFiniteInitialPolynomialMap (n + 1) σ A
      (relativeFreeFrobeniusFinitePolynomial D s n) =
        (relativeFreeDeltaStructure σ D).frobeniusLift^[n] (MvPolynomial.X (s, 0)) := by
  cases n with
  | zero => simp [relativeFreeFrobeniusFinitePolynomial, relativeFreeFiniteInitialPolynomialMap]
  | succ n =>
      rw [relativeFreeFrobenius_iterate_top_linear]
      simp only [relativeFreeFrobeniusFinitePolynomial, map_add, map_mul, map_pow, map_natCast]
      have hx : relativeFreeFiniteInitialPolynomialMap (n + 2) σ A
          (MvPolynomial.X (s, Fin.last (n + 1))) = MvPolynomial.X (s, n + 1) := by
        simp [relativeFreeFiniteInitialPolynomialMap]
      rw [hx]
      congr 1
      exact RingHom.congr_fun (relativeFreeFiniteStepInclusion_comp_initial (A := A) n σ) _

/-- 自由初期変数のφ^n像には第n段以下の変数しか現れない。 -/
theorem relativeFreeFrobenius_iterate_variable_bound (D : DeltaStructure p A) (s : σ) (n : ℕ)
    (z : σ × ℕ)
    (hz : z ∈ ((relativeFreeDeltaStructure σ D).frobeniusLift^[n]
      (MvPolynomial.X (s, 0))).vars) : z.2 ≤ n := by
  rw [← relativeFreeFrobeniusFinitePolynomial_image D s n] at hz
  change z ∈ (MvPolynomial.rename (fun x : σ × Fin (n + 1) => (x.1, x.2.val))
    (relativeFreeFrobeniusFinitePolynomial D s n)).vars at hz
  obtain ⟨⟨t, i⟩, _, he⟩ := MvPolynomial.mem_vars_rename _ _ hz
  have hn := i.isLt
  have hval := congrArg Prod.snd he
  change i.val = z.2 at hval
  omega

end SerrePositivity.BhattScholze

end RelativeFreeFrobeniusTopLinear

/-! ## 自由初期変数のWitt係数と最高δ変数の全段再帰式

正確なFrobenius線形表示を全ghost等式へ代入する。
-/

section RelativeFreeWittGhostRecurrence

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 相対自由δ環の初期変数に対して構成したWitt係数多項式。 -/
def relativeFreeWittGhostCoefficient (D : DeltaStructure p A) (s : σ) (n : ℕ) :
    RelativeFreeDeltaRing (R := A) σ :=
  (deltaWittGhostVector (relativeFreeDeltaStructure σ D) (MvPolynomial.X (s, 0))).coeff n

/-- 第0Witt係数は初期δ変数そのもの。 -/
@[simp] theorem relativeFreeWittGhostCoefficient_zero (D : DeltaStructure p A) (s : σ) :
    relativeFreeWittGhostCoefficient D s 0 = MvPolynomial.X (s, 0) := rfl

/-- 全深さで、Witt係数から最高δ変数を引いた差のp冪倍は下位係数だけの式。 -/
theorem relativeFreeWittGhostCoefficient_top_recurrence
    (D : DeltaStructure p A) (s : σ) (n : ℕ) :
    (p : RelativeFreeDeltaRing (R := A) σ) ^ (n + 1) *
      (relativeFreeWittGhostCoefficient D s (n + 1) - MvPolynomial.X (s, n + 1)) =
        relativeFreeFiniteInitialPolynomialMap (n + 1) σ A
          (relativeFreeFrobeniusLowerPolynomial D s n) -
            ∑ i ∈ Finset.range (n + 1), (p : RelativeFreeDeltaRing (R := A) σ) ^ i *
              relativeFreeWittGhostCoefficient D s i ^ (p ^ (n + 1 - i)) := by
  have hghost := deltaWittGhostCoefficients_ghost (relativeFreeDeltaStructure σ D)
    (MvPolynomial.X (s, 0)) (n + 1)
  have hcoeff (i : ℕ) : deltaWittGhostCoefficients (relativeFreeDeltaStructure σ D)
      (MvPolynomial.X (s, 0)) i = relativeFreeWittGhostCoefficient D s i := rfl
  rw [relativeFreeFrobenius_iterate_top_linear] at hghost
  simp only [hcoeff] at hghost
  rw [Finset.sum_range_succ] at hghost
  simp only [Nat.sub_self, pow_zero, pow_one] at hghost
  linear_combination -hghost

end SerrePositivity.BhattScholze

end RelativeFreeWittGhostRecurrence

/-! ## 全Witt係数と最高δ変数の差の下位変数所属

p乗算単射だけで係数の零判定を戻し、全段再帰式を強帰納する。
-/

section RelativeFreeWittGhostSupport

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

omit [Fact p.Prime] in
private theorem prime_pow_mul_injective
    (hp : Function.Injective (fun a : A => (p : A) * a)) (n : ℕ) :
    Function.Injective (fun a : A => (p : A) ^ n * a) := by
  induction n with
  | zero =>
      intro a b h
      simpa only [pow_zero, one_mul] using h
  | succ n ih =>
      intro a b h
      apply ih
      apply hp
      simpa only [pow_succ', mul_assoc] using h

private theorem vars_C_mul_regular {τ : Type*} (c : A)
    (hc : Function.Injective (fun a : A => c * a)) (f : MvPolynomial τ A) :
    (MvPolynomial.C c * f).vars = f.vars := by
  classical
  have hz (a : A) : c * a = 0 ↔ a = 0 :=
    ⟨fun h => hc (h.trans (mul_zero c).symm), fun h => by rw [h, mul_zero]⟩
  ext z
  simp only [MvPolynomial.mem_vars_iff_mem_support, MvPolynomial.mem_support_iff,
    MvPolynomial.coeff_C_mul, ne_eq, hz]

omit [Fact p.Prime] in
private theorem mem_supported_of_prime_pow_mul
    (hp : Function.Injective (fun a : A => (p : A) * a)) (n : ℕ)
    (f : RelativeFreeDeltaRing (R := A) σ) (s : Set (σ × ℕ))
    (hf : (p : RelativeFreeDeltaRing (R := A) σ) ^ n * f ∈ MvPolynomial.supported A s) :
    f ∈ MvPolynomial.supported A s := by
  have he : (p : RelativeFreeDeltaRing (R := A) σ) ^ n = MvPolynomial.C ((p : A) ^ n) := by
    rw [map_pow, map_natCast]
  have hv : ((p : RelativeFreeDeltaRing (R := A) σ) ^ n * f).vars = f.vars := by
    rw [he]
    exact vars_C_mul_regular _ (prime_pow_mul_injective hp n) f
  apply MvPolynomial.mem_supported.mpr
  rw [← hv]
  exact MvPolynomial.mem_supported.mp hf

/-- p乗算単射の下で、全Witt係数と最高δ変数の差は下位変数だけの多項式。 -/
theorem relativeFreeWittGhostCoefficient_sub_X_mem_supported (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (s : σ) (n : ℕ) :
    relativeFreeWittGhostCoefficient D s n - MvPolynomial.X (s, n) ∈
      MvPolynomial.supported A {z : σ × ℕ | z.2 < n} := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          simp only [relativeFreeWittGhostCoefficient_zero, sub_self]
          exact Subalgebra.zero_mem _
      | succ n =>
          let S := MvPolynomial.supported A {z : σ × ℕ | z.2 < n + 1}
          have hX (i : ℕ) (hi : i < n + 1) :
              (MvPolynomial.X (s, i) : RelativeFreeDeltaRing (R := A) σ) ∈ S := by
            apply Algebra.subset_adjoin
            exact ⟨(s, i), hi, rfl⟩
          have hcoef (i : ℕ) (hi : i < n + 1) : relativeFreeWittGhostCoefficient D s i ∈ S := by
            have hlow := (MvPolynomial.supported_mono (R := A)
              (fun z hz => Nat.lt_trans hz hi)) (ih i hi)
            have he := S.add_mem hlow (hX i hi)
            simpa only [sub_add_cancel] using he
          have hlower : relativeFreeFiniteInitialPolynomialMap (n + 1) σ A
              (relativeFreeFrobeniusLowerPolynomial D s n) ∈ S := by
            apply MvPolynomial.mem_supported.mpr
            intro z hz
            change z ∈ (MvPolynomial.rename (fun x : σ × Fin (n + 1) => (x.1, x.2.val))
              (relativeFreeFrobeniusLowerPolynomial D s n)).vars at hz
            obtain ⟨⟨t, i⟩, _, he⟩ := MvPolynomial.mem_vars_rename _ _ hz
            have hi := i.isLt
            have hval := congrArg Prod.snd he
            change i.val = z.2 at hval
            change z.2 < n + 1
            omega
          have hsum : (∑ i ∈ Finset.range (n + 1), (p : RelativeFreeDeltaRing (R := A) σ) ^ i *
              relativeFreeWittGhostCoefficient D s i ^ (p ^ (n + 1 - i))) ∈ S := by
            apply S.sum_mem
            intro i hi
            exact S.mul_mem (S.pow_mem (S.natCast_mem p) i)
              (S.pow_mem (hcoef i (Finset.mem_range.mp hi)) _)
          apply mem_supported_of_prime_pow_mul hp (n + 1)
          rw [relativeFreeWittGhostCoefficient_top_recurrence]
          exact S.sub_mem hlower hsum

/-- 各Witt係数の変数は第n段以下。整域性・G4は不要。 -/
theorem relativeFreeWittGhostCoefficient_variable_bound (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (s : σ) (n : ℕ)
    (z : σ × ℕ) (hz : z ∈ (relativeFreeWittGhostCoefficient D s n).vars) : z.2 ≤ n := by
  classical
  have hlow := relativeFreeWittGhostCoefficient_sub_X_mem_supported D hp s n
  have hX : (MvPolynomial.X (s, n) : RelativeFreeDeltaRing (R := A) σ) ∈
      MvPolynomial.supported A {z : σ × ℕ | z.2 ≤ n} := by
    apply Algebra.subset_adjoin
    exact ⟨(s, n), (by change n ≤ n; exact le_rfl), rfl⟩
  have hlow' := (MvPolynomial.supported_mono (R := A) (fun z hz => Nat.le_of_lt hz)) hlow
  have he := (MvPolynomial.supported A {z : σ × ℕ | z.2 ≤ n}).add_mem hlow' hX
  rw [sub_add_cancel] at he
  exact MvPolynomial.mem_supported.mp he hz

end SerrePositivity.BhattScholze

end RelativeFreeWittGhostSupport

/-! ## 全Witt係数の最高δ変数係数1の有限三角形表示

下位変数所属から初期有限多項式を取り出し、表示の一意性も確認する。
-/

section RelativeFreeWittGhostTriangular

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 全段でWitt係数は最高δ変数と、その手前の有限多項式の和。 -/
theorem exists_relativeFreeWittGhostLowerPolynomial (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (s : σ) (n : ℕ) :
    ∃ c : MvPolynomial (σ × Fin n) A, relativeFreeWittGhostCoefficient D s n =
      MvPolynomial.X (s, n) + relativeFreeFiniteInitialPolynomialMap n σ A c := by
  let f := relativeFreeWittGhostCoefficient D s n - MvPolynomial.X (s, n)
  have hs := MvPolynomial.mem_supported.mp
    (relativeFreeWittGhostCoefficient_sub_X_mem_supported D hp s n)
  let ι : σ × Fin n → σ × ℕ := fun x => (x.1, x.2.val)
  have hi : Function.Injective ι := by
    intro x y h
    exact Prod.ext (congrArg (fun z : σ × ℕ => z.1) h)
      (Fin.ext (congrArg (fun z : σ × ℕ => z.2) h))
  have hv : (f.vars : Set (σ × ℕ)) ⊆ Set.range ι := by
    intro z hz
    have hz' : z.2 < n := hs hz
    exact ⟨(z.1, ⟨z.2, hz'⟩), rfl⟩
  obtain ⟨c, hc⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range f ι hi hv
  change relativeFreeFiniteInitialPolynomialMap n σ A c =
    relativeFreeWittGhostCoefficient D s n - MvPolynomial.X (s, n) at hc
  refine ⟨c, ?_⟩
  rw [hc]
  ring

/-- 全段の三角形表示で現れる初期n段の具体的な下位多項式。 -/
def relativeFreeWittGhostLowerPolynomial (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (s : σ) (n : ℕ) :
    MvPolynomial (σ × Fin n) A :=
  Classical.choose (exists_relativeFreeWittGhostLowerPolynomial D hp s n)

/-- 構成した下位多項式による、最高δ変数係数1の全段の正確な表示。 -/
theorem relativeFreeWittGhostCoefficient_eq_X_add_lower (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (s : σ) (n : ℕ) :
    relativeFreeWittGhostCoefficient D s n = MvPolynomial.X (s, n) +
      relativeFreeFiniteInitialPolynomialMap n σ A
        (relativeFreeWittGhostLowerPolynomial D hp s n) :=
  Classical.choose_spec (exists_relativeFreeWittGhostLowerPolynomial D hp s n)

/-- この初期n段の下位多項式表示は一意。 -/
theorem relativeFreeWittGhostLowerPolynomial_unique (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (s : σ) (n : ℕ)
    (c : MvPolynomial (σ × Fin n) A)
    (hc : relativeFreeWittGhostCoefficient D s n =
      MvPolynomial.X (s, n) + relativeFreeFiniteInitialPolynomialMap n σ A c) :
    c = relativeFreeWittGhostLowerPolynomial D hp s n := by
  apply relativeFreeFiniteInitialPolynomialMap_injective n σ
  exact add_left_cancel (hc.symm.trans (relativeFreeWittGhostCoefficient_eq_X_add_lower D hp s n))

/-- 第0段の下位多項式は零。 -/
@[simp] theorem relativeFreeWittGhostLowerPolynomial_zero (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (s : σ) :
    relativeFreeWittGhostLowerPolynomial D hp s 0 = 0 := by
  symm
  apply relativeFreeWittGhostLowerPolynomial_unique
  simp only [relativeFreeWittGhostCoefficient_zero, map_zero, add_zero]

end SerrePositivity.BhattScholze

end RelativeFreeWittGhostTriangular

/-! ## 全Witt座標とδ変数の三角形代数同型

下位有限多項式を評価して逆変数を強帰納で構成する。
-/

section RelativeFreeWittCoordinateChange

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- δ変数を構成済みWitt係数へ送る相対多項式代数射。 -/
def relativeFreeWittCoordinateMap (D : DeltaStructure p A) :
    RelativeFreeDeltaRing (R := A) σ →ₐ[A] RelativeFreeDeltaRing (R := A) σ :=
  MvPolynomial.aeval (fun z => relativeFreeWittGhostCoefficient D z.1 z.2)

/-- 第n逆変数は、初期n段の逆変数による下位多項式評価を引いて構成する。 -/
def relativeFreeWittInverseVariable (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) :
    ℕ → σ → RelativeFreeDeltaRing (R := A) σ :=
  Nat.strongRec (fun n rec s => MvPolynomial.X (s, n) -
    MvPolynomial.aeval (fun z : σ × Fin n => rec z.2.val z.2.isLt z.1)
      (relativeFreeWittGhostLowerPolynomial D hp s n))

/-- 段数の強帰納による逆変数の評価式。 -/
theorem relativeFreeWittInverseVariable_eq (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (n : ℕ) (s : σ) :
    relativeFreeWittInverseVariable D hp n s = MvPolynomial.X (s, n) -
      MvPolynomial.aeval (fun z : σ × Fin n => relativeFreeWittInverseVariable D hp z.2.val z.1)
        (relativeFreeWittGhostLowerPolynomial D hp s n) := by
  rw [relativeFreeWittInverseVariable, Nat.strongRec_eq]
  rfl

/-- 強帰納で構成した逆変数を指定する相対多項式代数射。 -/
def relativeFreeWittInverseMap (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) :
    RelativeFreeDeltaRing (R := A) σ →ₐ[A] RelativeFreeDeltaRing (R := A) σ :=
  MvPolynomial.aeval (fun z => relativeFreeWittInverseVariable D hp z.2 z.1)

/-- 逆代数射は全Witt係数を元のδ変数へ戻す。 -/
theorem relativeFreeWittInverseMap_coefficient (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (s : σ) (n : ℕ) :
    relativeFreeWittInverseMap D hp (relativeFreeWittGhostCoefficient D s n) =
      MvPolynomial.X (s, n) := by
  rw [relativeFreeWittGhostCoefficient_eq_X_add_lower D hp, map_add]
  simp only [relativeFreeWittInverseMap, MvPolynomial.aeval_X]
  rw [relativeFreeWittInverseVariable_eq]
  simp only [relativeFreeFiniteInitialPolynomialMap, MvPolynomial.aeval_rename]
  let t := MvPolynomial.aeval
    (fun z : σ × Fin n => relativeFreeWittInverseVariable D hp z.2.val z.1)
    (relativeFreeWittGhostLowerPolynomial D hp s n)
  change MvPolynomial.X (s, n) - t + t = MvPolynomial.X (s, n)
  exact sub_add_cancel _ _

/-- 元の座標代数射は全逆変数をδ変数へ戻す。 -/
theorem relativeFreeWittCoordinateMap_inverseVariable (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (n : ℕ) (s : σ) :
    relativeFreeWittCoordinateMap D (relativeFreeWittInverseVariable D hp n s) =
      MvPolynomial.X (s, n) := by
  induction n using Nat.strong_induction_on generalizing s with
  | h n ih =>
      rw [relativeFreeWittInverseVariable_eq, map_sub]
      have hx : relativeFreeWittCoordinateMap D (MvPolynomial.X (s, n)) =
          relativeFreeWittGhostCoefficient D s n := MvPolynomial.aeval_X _ _
      rw [hx, relativeFreeWittGhostCoefficient_eq_X_add_lower D hp]
      have he : relativeFreeWittCoordinateMap D
          (MvPolynomial.aeval
            (fun z : σ × Fin n => relativeFreeWittInverseVariable D hp z.2.val z.1)
            (relativeFreeWittGhostLowerPolynomial D hp s n)) =
          relativeFreeFiniteInitialPolynomialMap n σ A
            (relativeFreeWittGhostLowerPolynomial D hp s n) := by
        change ((relativeFreeWittCoordinateMap D).comp (MvPolynomial.aeval _)) _ = _
        rw [MvPolynomial.comp_aeval]
        have hv : (fun z : σ × Fin n => relativeFreeWittCoordinateMap D
            (relativeFreeWittInverseVariable D hp z.2.val z.1)) =
            fun z => (MvPolynomial.X (z.1, z.2.val) : RelativeFreeDeltaRing (R := A) σ) := by
          funext z
          exact ih z.2.val z.2.isLt z.1
        rw [hv]
        simp only [relativeFreeFiniteInitialPolynomialMap, MvPolynomial.rename_eq_aeval]
        rfl
      rw [he]
      ring

/-- 逆座標代数射と座標代数射の合成は恒等。 -/
theorem relativeFreeWittInverseMap_comp_coordinateMap (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) :
    (relativeFreeWittInverseMap D hp).comp (relativeFreeWittCoordinateMap (σ := σ) D) =
      AlgHom.id A _ := by
  apply MvPolynomial.algHom_ext
  intro z
  simp only [AlgHom.comp_apply, relativeFreeWittCoordinateMap, MvPolynomial.aeval_X,
    relativeFreeWittInverseMap_coefficient, AlgHom.id_apply]

/-- 座標代数射と逆座標代数射の合成も恒等。 -/
theorem relativeFreeWittCoordinateMap_comp_inverseMap (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) :
    (relativeFreeWittCoordinateMap D).comp (relativeFreeWittInverseMap (σ := σ) D hp) =
      AlgHom.id A _ := by
  apply MvPolynomial.algHom_ext
  intro z
  simp only [AlgHom.comp_apply, relativeFreeWittInverseMap, MvPolynomial.aeval_X,
    relativeFreeWittCoordinateMap_inverseVariable, AlgHom.id_apply]

/-- 全Witt座標への三角形置換は、任意添字族での実際のA代数同型（BS 著者版 Remark 2.14 の p 正則な δ 基底上の相対版）。 -/
def relativeFreeWittCoordinateEquiv (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) :
    RelativeFreeDeltaRing (R := A) σ ≃ₐ[A] RelativeFreeDeltaRing (R := A) σ :=
  AlgEquiv.ofAlgHom (relativeFreeWittCoordinateMap D) (relativeFreeWittInverseMap D hp)
    (relativeFreeWittCoordinateMap_comp_inverseMap D hp)
    (relativeFreeWittInverseMap_comp_coordinateMap D hp)

/-- 代数同型は各δ変数を対応するWitt係数へ送る。 -/
@[simp] theorem relativeFreeWittCoordinateEquiv_X (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (s : σ) (n : ℕ) :
    relativeFreeWittCoordinateEquiv D hp (MvPolynomial.X (s, n)) =
      relativeFreeWittGhostCoefficient D s n := by
  exact MvPolynomial.aeval_X _ _

/-- 逆同型は各Witt係数を対応するδ変数へ戻す。 -/
@[simp] theorem relativeFreeWittCoordinateEquiv_symm_coefficient (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (s : σ) (n : ℕ) :
    (relativeFreeWittCoordinateEquiv D hp).symm (relativeFreeWittGhostCoefficient D s n) =
      MvPolynomial.X (s, n) :=
  relativeFreeWittInverseMap_coefficient D hp s n

end SerrePositivity.BhattScholze

end RelativeFreeWittCoordinateChange

/-! ## 逆Witt変数の段数と初期変数部分代数への制限

三角形同型の順逆射が各初期変数部分代数を保存する。
-/

section RelativeFreeWittInverseSupport

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

private theorem aeval_mem_supported {τ : Type*}
    (S : Subalgebra A (RelativeFreeDeltaRing (R := A) σ))
    (v : τ → RelativeFreeDeltaRing (R := A) σ) (hv : ∀ i, v i ∈ S) (c : MvPolynomial τ A) :
    MvPolynomial.aeval v c ∈ S := by
  exact MvPolynomial.eval₂_mem (fun _ _ => S.algebraMap_mem _) hv

/-- 第n逆変数は第n段以下の変数だけの多項式。 -/
theorem relativeFreeWittInverseVariable_mem_supported (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (n : ℕ) (s : σ) :
    relativeFreeWittInverseVariable D hp n s ∈
      MvPolynomial.supported A {z : σ × ℕ | z.2 ≤ n} := by
  classical
  induction n using Nat.strong_induction_on generalizing s with
  | h n ih =>
      let S := MvPolynomial.supported A {z : σ × ℕ | z.2 ≤ n}
      rw [relativeFreeWittInverseVariable_eq]
      apply S.sub_mem
      · apply Algebra.subset_adjoin
        exact ⟨(s, n), (by change n ≤ n; exact le_rfl), rfl⟩
      · apply aeval_mem_supported
        intro z
        exact (MvPolynomial.supported_mono (R := A)
          (fun x hx => Nat.le_trans hx (Nat.le_of_lt z.2.isLt)))
          (ih z.2.val z.2.isLt z.1)

/-- 構成した逆変数の変数段数上界。 -/
theorem relativeFreeWittInverseVariable_variable_bound (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (n : ℕ) (s : σ)
    (z : σ × ℕ) (hz : z ∈ (relativeFreeWittInverseVariable D hp n s).vars) : z.2 ≤ n :=
  MvPolynomial.mem_supported.mp (relativeFreeWittInverseVariable_mem_supported D hp n s) hz

/-- 順座標射は任意初期N段の変数部分代数を保存する。 -/
theorem relativeFreeWittCoordinateMap_mem_supported (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (N : ℕ)
    (f : RelativeFreeDeltaRing (R := A) σ)
    (hf : f ∈ MvPolynomial.supported A {z : σ × ℕ | z.2 < N}) :
    relativeFreeWittCoordinateMap D f ∈ MvPolynomial.supported A {z : σ × ℕ | z.2 < N} := by
  let S := MvPolynomial.supported A {z : σ × ℕ | z.2 < N}
  have h : S ≤ S.comap (relativeFreeWittCoordinateMap D) := by
    apply Algebra.adjoin_le
    intro v hv
    obtain ⟨z, hz, rfl⟩ := hv
    change relativeFreeWittCoordinateMap D (MvPolynomial.X z) ∈ S
    rw [relativeFreeWittCoordinateMap, MvPolynomial.aeval_X]
    apply MvPolynomial.mem_supported.mpr
    intro x hx
    exact Nat.lt_of_le_of_lt (relativeFreeWittGhostCoefficient_variable_bound D hp z.1 z.2 x hx) hz
  exact h hf

/-- 逆座標射も任意初期N段の変数部分代数を保存する。 -/
theorem relativeFreeWittInverseMap_mem_supported (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (N : ℕ)
    (f : RelativeFreeDeltaRing (R := A) σ)
    (hf : f ∈ MvPolynomial.supported A {z : σ × ℕ | z.2 < N}) :
    relativeFreeWittInverseMap D hp f ∈ MvPolynomial.supported A {z : σ × ℕ | z.2 < N} := by
  let S := MvPolynomial.supported A {z : σ × ℕ | z.2 < N}
  have h : S ≤ S.comap (relativeFreeWittInverseMap D hp) := by
    apply Algebra.adjoin_le
    intro v hv
    obtain ⟨z, hz, rfl⟩ := hv
    change relativeFreeWittInverseMap D hp (MvPolynomial.X z) ∈ S
    rw [relativeFreeWittInverseMap, MvPolynomial.aeval_X]
    exact (MvPolynomial.supported_mono (R := A) (fun x hx => Nat.lt_of_le_of_lt hx hz))
      (relativeFreeWittInverseVariable_mem_supported D hp z.2 z.1)
  exact h hf

/-- 全Witt座標同型は、任意初期N段の変数部分代数の実際の代数同型に制限できる。 -/
def relativeFreeWittSupportedEquiv (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (N : ℕ) :
    MvPolynomial.supported A {z : σ × ℕ | z.2 < N} ≃ₐ[A]
      MvPolynomial.supported A {z : σ × ℕ | z.2 < N} where
  toFun f := ⟨relativeFreeWittCoordinateMap D f.val,
    relativeFreeWittCoordinateMap_mem_supported D hp N f.val f.property⟩
  invFun f := ⟨relativeFreeWittInverseMap D hp f.val,
    relativeFreeWittInverseMap_mem_supported D hp N f.val f.property⟩
  left_inv f := by
    apply Subtype.ext
    exact (relativeFreeWittCoordinateEquiv D hp).symm_apply_apply f.val
  right_inv f := by
    apply Subtype.ext
    exact (relativeFreeWittCoordinateEquiv D hp).apply_symm_apply f.val
  map_mul' f g := by apply Subtype.ext; exact map_mul _ _ _
  map_add' f g := by apply Subtype.ext; exact map_add _ _ _
  commutes' a := by apply Subtype.ext; exact AlgHom.commutes _ a

/-- 制限した代数同型の標準包含図式。 -/
theorem relativeFreeWittSupportedEquiv_coe (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (N : ℕ)
    (f : MvPolynomial.supported A {z : σ × ℕ | z.2 < N}) :
    (relativeFreeWittSupportedEquiv D hp N f : RelativeFreeDeltaRing (R := A) σ) =
      relativeFreeWittCoordinateMap D (f : RelativeFreeDeltaRing (R := A) σ) := rfl

end SerrePositivity.BhattScholze

end RelativeFreeWittInverseSupport

/-! ## 通常有限多項式環上のWitt座標代数同型

初期変数部分代数との同型で制限済み座標同型を移す。
-/

section RelativeFreeFiniteWittCoordinateChange

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 初期変数部分集合と有限段添字の標準同型。 -/
def relativeFreeFiniteSupportedIndexEquiv (N : ℕ) (σ : Type v) :
    {z : σ × ℕ // z.2 < N} ≃ σ × Fin N where
  toFun z := (z.val.1, ⟨z.val.2, z.property⟩)
  invFun z := ⟨(z.1, z.2.val), z.2.isLt⟩
  left_inv z := by cases z; rfl
  right_inv z := by cases z; rfl

/-- 初期N段の有限多項式環と、全変数環の初期部分代数の標準同型。 -/
def relativeFreeFiniteSupportedEquiv (N : ℕ) (σ : Type v) (A : Type u) [CommRing A] :
    MvPolynomial (σ × Fin N) A ≃ₐ[A] MvPolynomial.supported A {z : σ × ℕ | z.2 < N} :=
  (MvPolynomial.renameEquiv A (relativeFreeFiniteSupportedIndexEquiv N σ).symm).trans
    (MvPolynomial.supportedEquivMvPolynomial {z : σ × ℕ | z.2 < N}).symm

/-- 初期部分代数同型の係数包含は既存の標準初期多項式射そのもの。 -/
theorem relativeFreeFiniteSupportedEquiv_coe (N : ℕ) (f : MvPolynomial (σ × Fin N) A) :
    (relativeFreeFiniteSupportedEquiv N σ A f : RelativeFreeDeltaRing (R := A) σ) =
      relativeFreeFiniteInitialPolynomialMap N σ A f := by
  have he : (MvPolynomial.supported A {z : σ × ℕ | z.2 < N}).val.comp
      (relativeFreeFiniteSupportedEquiv N σ A).toAlgHom =
        relativeFreeFiniteInitialPolynomialMap N σ A := by
    apply MvPolynomial.algHom_ext
    intro z
    change ((MvPolynomial.supportedEquivMvPolynomial (R := A) {z : σ × ℕ | z.2 < N}).symm
      (MvPolynomial.rename (relativeFreeFiniteSupportedIndexEquiv N σ).symm
        (MvPolynomial.X z))).val = _
    rw [MvPolynomial.rename_X, MvPolynomial.supportedEquivMvPolynomial_symm_X]
    simp only [relativeFreeFiniteInitialPolynomialMap, MvPolynomial.rename_X]
    rfl
  exact AlgHom.congr_fun he f

/-- 初期N段の通常多項式環上の実際のWitt座標代数同型（BS 著者版 Remark 2.14 の p 正則な δ 基底上の相対版で有限段の座標）。 -/
def relativeFreeFiniteWittCoordinateEquiv (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (N : ℕ) :
    MvPolynomial (σ × Fin N) A ≃ₐ[A] MvPolynomial (σ × Fin N) A :=
  (relativeFreeFiniteSupportedEquiv N σ A).trans
    ((relativeFreeWittSupportedEquiv D hp N).trans (relativeFreeFiniteSupportedEquiv N σ A).symm)

/-- 有限座標同型と全座標射の標準包含図式。 -/
theorem relativeFreeFiniteWittCoordinateEquiv_initial (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (N : ℕ)
    (f : MvPolynomial (σ × Fin N) A) :
    relativeFreeFiniteInitialPolynomialMap N σ A (relativeFreeFiniteWittCoordinateEquiv D hp N f) =
      relativeFreeWittCoordinateMap D (relativeFreeFiniteInitialPolynomialMap N σ A f) := by
  let F := relativeFreeFiniteSupportedEquiv N σ A
  let E := relativeFreeWittSupportedEquiv (σ := σ) D hp N
  calc
    _ = (F (relativeFreeFiniteWittCoordinateEquiv D hp N f) : RelativeFreeDeltaRing (R := A) σ) :=
      (relativeFreeFiniteSupportedEquiv_coe N _).symm
    _ = (E (F f) : RelativeFreeDeltaRing (R := A) σ) := by
      change (F (F.symm (E (F f))) : RelativeFreeDeltaRing (R := A) σ) = _
      rw [F.apply_symm_apply]
    _ = relativeFreeWittCoordinateMap D (F f : RelativeFreeDeltaRing (R := A) σ) :=
      relativeFreeWittSupportedEquiv_coe D hp N (F f)
    _ = _ := by rw [relativeFreeFiniteSupportedEquiv_coe]

/-- 有限逆座標同型の標準包含図式。 -/
theorem relativeFreeFiniteWittCoordinateEquiv_symm_initial (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (N : ℕ)
    (f : MvPolynomial (σ × Fin N) A) :
    relativeFreeFiniteInitialPolynomialMap N σ A
      ((relativeFreeFiniteWittCoordinateEquiv D hp N).symm f) =
        relativeFreeWittInverseMap D hp (relativeFreeFiniteInitialPolynomialMap N σ A f) := by
  let E := relativeFreeFiniteWittCoordinateEquiv (σ := σ) D hp N
  have he := relativeFreeFiniteWittCoordinateEquiv_initial D hp N (E.symm f)
  rw [E.apply_symm_apply] at he
  have hc := AlgHom.congr_fun (relativeFreeWittInverseMap_comp_coordinateMap D hp)
    (relativeFreeFiniteInitialPolynomialMap N σ A (E.symm f))
  simp only [AlgHom.comp_apply, AlgHom.id_apply] at hc
  exact hc.symm.trans (congrArg (relativeFreeWittInverseMap D hp) he.symm)

/-- 有限座標同型は各有限δ変数を対応する全Witt係数へ移す。 -/
theorem relativeFreeFiniteWittCoordinateEquiv_X_initial (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (N : ℕ) (s : σ) (i : Fin N) :
    relativeFreeFiniteInitialPolynomialMap N σ A
      (relativeFreeFiniteWittCoordinateEquiv D hp N (MvPolynomial.X (s, i))) =
        relativeFreeWittGhostCoefficient D s i.val := by
  rw [relativeFreeFiniteWittCoordinateEquiv_initial]
  have hx : relativeFreeFiniteInitialPolynomialMap N σ A (MvPolynomial.X (s, i)) =
      MvPolynomial.X (s, i.val) := by simp [relativeFreeFiniteInitialPolynomialMap]
  rw [hx, relativeFreeWittCoordinateMap, MvPolynomial.aeval_X]

end SerrePositivity.BhattScholze

end RelativeFreeFiniteWittCoordinateChange

/-! ## 基底係数のWitt像と逆座標射での固定

相対係数δ射の自然性を使い、基底Witt係数を直接比較する。
-/

section RelativeFreeWittCoefficientNaturality

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 相対自由環の基底係数のWitt元は、基底Witt元の係数包含像。 -/
theorem deltaWittGhostVector_relativeFree_C (D : DeltaStructure p A)
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (a : A) :
    deltaWittGhostVector (relativeFreeDeltaStructure σ D) (MvPolynomial.C a) =
      WittVector.map MvPolynomial.C (deltaWittGhostVector D a) :=
  (deltaWittGhostVector_map D (relativeFreeDeltaStructure σ D) MvPolynomial.C
    (relativeFreeDeltaStructure_C_isDeltaHom σ D) hg a).symm

/-- 全基底Witt係数は相対自由環への通常係数像に一致する。 -/
theorem deltaWittGhostVector_relativeFree_C_coeff (D : DeltaStructure p A)
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (a : A) (n : ℕ) :
    (deltaWittGhostVector (relativeFreeDeltaStructure σ D) (MvPolynomial.C a)).coeff n =
      MvPolynomial.C ((deltaWittGhostVector D a).coeff n) := by
  rw [deltaWittGhostVector_relativeFree_C D hg, WittVector.map_coeff]

/-- 逆座標射は基底係数の全Witt係数を固定する。 -/
theorem relativeFreeWittInverseMap_coefficient_C (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (a : A) (n : ℕ) :
    relativeFreeWittInverseMap D hp
      ((deltaWittGhostVector (relativeFreeDeltaStructure σ D) (MvPolynomial.C a)).coeff n) =
        MvPolynomial.C ((deltaWittGhostVector D a).coeff n) := by
  rw [deltaWittGhostVector_relativeFree_C_coeff D hg]
  exact AlgHom.commutes (relativeFreeWittInverseMap D hp) _

/-- 逆座標係数射は基底係数のWitt元全体も固定する。 -/
theorem relativeFreeWittInverseMap_wittVector_C (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (a : A) :
    WittVector.map (relativeFreeWittInverseMap D hp).toRingHom
      (deltaWittGhostVector (relativeFreeDeltaStructure σ D) (MvPolynomial.C a)) =
        deltaWittGhostVector (relativeFreeDeltaStructure σ D) (MvPolynomial.C a) := by
  apply WittVector.ext
  intro n
  rw [WittVector.map_coeff]
  change relativeFreeWittInverseMap D hp
    ((deltaWittGhostVector (relativeFreeDeltaStructure σ D) (MvPolynomial.C a)).coeff n) = _
  rw [relativeFreeWittInverseMap_coefficient_C D hp hg,
    deltaWittGhostVector_relativeFree_C_coeff D hg]

end SerrePositivity.BhattScholze

end RelativeFreeWittCoefficientNaturality

/-! ## 任意の元のδjetとWitt jetの三角形比較

自由変数の三角形表示をδ評価し、通常射の下での下位jet消滅を扱う。
-/

section DeltaWittJetComparison

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 任意の元の第nWitt係数は、δ^nと下位δjetの有限多項式評価の和。 -/
theorem deltaWittGhostVector_coeff_eq_delta_iterate_add_lower (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A)) (a : A) (n : ℕ) :
    (deltaWittGhostVector D a).coeff n = D.delta^[n] a +
      MvPolynomial.eval₂Hom (RingHom.id A) (fun z : Unit × Fin n => D.delta^[z.2.val] a)
        (relativeFreeWittGhostLowerPolynomial D hp () n) := by
  let f := relativeFreeDeltaEval D (RingHom.id A) (fun _ : Unit => a)
  have hf : (relativeFreeDeltaStructure Unit D).IsDeltaHom D f :=
    relativeFreeDeltaEval_isDeltaHom D D (RingHom.id A) (fun _ => rfl) (fun _ => a)
  have he := deltaWittGhostVector_coeff_map (relativeFreeDeltaStructure Unit D) D f hf hg
    (MvPolynomial.X ((), 0)) n
  have hx : f (MvPolynomial.X ((), 0)) = a := by simp [f]
  rw [hx] at he
  change f (relativeFreeWittGhostCoefficient D () n) = _ at he
  rw [relativeFreeWittGhostCoefficient_eq_X_add_lower D hp, map_add] at he
  simpa only [f, relativeFreeDeltaEval_X, relativeFreeDeltaEval,
    relativeFreeFiniteInitialPolynomialMap, MvPolynomial.eval₂Hom_rename,
    MvPolynomial.eval₂Hom_X', Function.comp_def] using he.symm

/-- 自由三角形補正多項式の零δjetでの評価は零。 -/
theorem deltaWittGhostLowerPolynomial_eval_zero (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A)) (n : ℕ) :
    MvPolynomial.eval₂Hom (RingHom.id A) (fun _ : Unit × Fin n => (0 : A))
      (relativeFreeWittGhostLowerPolynomial D hp () n) = 0 := by
  have hi (i : ℕ) : D.delta^[i] (0 : A) = 0 := by
    induction i with
    | zero => rfl
    | succ i ih => rw [Function.iterate_succ_apply', ih, D.delta_zero]
  have hw : deltaWittGhostVector D (0 : A) = 0 := (deltaWittGhostRingHom D hg).map_zero
  have he := deltaWittGhostVector_coeff_eq_delta_iterate_add_lower D hp hg (0 : A) n
  rw [hw, WittVector.zero_coeff, hi, zero_add] at he
  have hv : (fun z : Unit × Fin n => D.delta^[z.2.val] (0 : A)) = fun _ => 0 := by
    funext z
    exact hi z.2.val
  rw [hv] at he
  exact he.symm

/-- 下位δjetを消す任意通常射では、第nWitt係数とδ^nの像が一致する。 -/
theorem deltaWittGhostVector_coeff_map_eq_of_lower_jets_zero {B : Type v} [CommRing B]
    (D : DeltaStructure p A) (hp : Function.Injective (fun a : A => (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (q : A →+* B) (a : A) (n : ℕ) (hjets : ∀ i < n, q (D.delta^[i] a) = 0) :
    q ((deltaWittGhostVector D a).coeff n) = q (D.delta^[n] a) := by
  rw [deltaWittGhostVector_coeff_eq_delta_iterate_add_lower D hp hg, map_add,
    MvPolynomial.map_eval₂Hom]
  have hv : (fun z : Unit × Fin n => q (D.delta^[z.2.val] a)) = fun _ => 0 := by
    funext z
    exact hjets z.2.val z.2.isLt
  rw [hv]
  have he := congrArg q (deltaWittGhostLowerPolynomial_eval_zero D hp hg n)
  rw [MvPolynomial.map_eval₂Hom, map_zero] at he
  rw [he, add_zero]

/-- 有限深さの全δjet消滅と全Witt係数消滅は任意通常射の下で同値。 -/
theorem deltaWittGhostVector_jets_zero_iff {B : Type v} [CommRing B]
    (D : DeltaStructure p A) (hp : Function.Injective (fun a : A => (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (q : A →+* B) (a : A) (N : ℕ) :
    (∀ i ≤ N, q (D.delta^[i] a) = 0) ↔
      (∀ i ≤ N, q ((deltaWittGhostVector D a).coeff i) = 0) := by
  constructor
  · intro h i hi
    rw [deltaWittGhostVector_coeff_map_eq_of_lower_jets_zero D hp hg q a i
      (fun j hj => h j (Nat.le_trans (Nat.le_of_lt hj) hi))]
    exact h i hi
  · intro h i hi
    induction i using Nat.strong_induction_on with
    | h i ih =>
        have he := deltaWittGhostVector_coeff_map_eq_of_lower_jets_zero D hp hg q a i
          (fun j hj => ih j hj (Nat.le_trans (Nat.le_of_lt hj) hi))
        rw [h i hi] at he
        exact he.symm

/-- 有限δjet消滅は、係数射を適用したWitt元の対応する切り詰めが零になる条件。 -/
theorem deltaWittGhostVector_jets_zero_iff_truncate_map_zero {B : Type v} [CommRing B]
    (D : DeltaStructure p A) (hp : Function.Injective (fun a : A => (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (q : A →+* B) (a : A) (N : ℕ) :
    (∀ i ≤ N, q (D.delta^[i] a) = 0) ↔
      WittVector.truncate (N + 1) (WittVector.map q (deltaWittGhostVector D a)) = 0 := by
  rw [deltaWittGhostVector_jets_zero_iff D hp hg]
  change _ ↔ WittVector.map q (deltaWittGhostVector D a) ∈ RingHom.ker (WittVector.truncate (N + 1))
  rw [WittVector.mem_ker_truncate]
  simp only [WittVector.map_coeff, Nat.lt_succ_iff]

end SerrePositivity.BhattScholze

end DeltaWittJetComparison

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Rem 2.14" (partial := special) "相対自由 δ 環の Witt 座標（δ_n 変数による多項式表示）の相対版。André の補題の経路（Thm 7.14 → Thm 7.4）の計算で使う。目標に必要な証明済みの部品（調整役の判定、11-07） ／ DOC1 照合：ok 2 件"] _root_.SerrePositivity.BhattScholze.relativeFreeFiniteWittCoordinateEquiv
attribute [cite BS19 "Rem 2.14" (partial := special) "相対自由 δ 環の Witt 座標（δ_n 変数による多項式表示）の相対版。André の補題の経路（Thm 7.14 → Thm 7.4）の計算で使う。目標に必要な証明済みの部品（調整役の判定、11-07） ／ DOC1 照合：ok 2 件"] _root_.SerrePositivity.BhattScholze.relativeFreeWittCoordinateEquiv
