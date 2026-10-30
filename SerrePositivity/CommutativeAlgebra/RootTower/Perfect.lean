module

public import SerrePositivity.CommutativeAlgebra.RootTower.Stage
public import Mathlib.FieldTheory.PerfectClosure
public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-! # 根の塔から完全環への標準写像

## 概要

標数 p の完全環 C への A 代数では、各パラメータ t_i の一意な p^n 乗根 `perfectRoot` を選べる。これが各有限段の関係式と遷移写像に両立するので、有限段から C への A 代数準同型 `towerStageToPerfect` と、塔全体からの準同型 `towerToPerfect` が得られ、どちらも一意である。有限段が標数 p なら p 冪は C の像に入り、適当な条件のもとで写像は単射である。

## 方針

根は Mathlib の `iterateFrobeniusEquiv` の逆で取る。局所性・正則性・長さの性質は使わない。

## 規約

名前空間は `SerrePositivity.Section2`（RootTower の他のファイルと同じ）。

## 使われ方

論文の定理 2.5 の等標数の場合（D の perfection への適用、Paper/Section2/PerfectApproximation ほか）。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.Section2
open MvPolynomial

variable (A C : Type u) [CommRing A] [CommRing C] [Algebra A C]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime] [CharP C p] [PerfectRing C p]

/-- 完全環内での `tᵢ` の一意な `pⁿ` 乗根。 -/
noncomputable def perfectRoot (n : ℕ) (i : Fin h) : C :=
  (iterateFrobeniusEquiv C p n).symm (algebraMap A C (t i))

/-- 選んだ根は各段の定義関係式を満たす。 -/
theorem perfectRoot_pow (n : ℕ) (i : Fin h) :
    perfectRoot A C t p n i ^ (p ^ n) = algebraMap A C (t i) :=
  (iterateFrobeniusEquiv C p n).apply_symm_apply _

/-- 根の選択は塔の遷移写像と両立する。 -/
theorem perfectRoot_compatible (a b : ℕ) (hab : a ≤ b) (i : Fin h) :
    perfectRoot A C t p b i ^ (p ^ (b - a)) = perfectRoot A C t p a i := by
  apply (iterateFrobeniusEquiv C p a).injective
  change (perfectRoot A C t p b i ^ (p ^ (b - a))) ^ (p ^ a) =
    perfectRoot A C t p a i ^ (p ^ a)
  rw [← pow_mul, ← pow_add, Nat.sub_add_cancel hab, perfectRoot_pow, perfectRoot_pow]

/-- 塔の一つの段から完全環への代数準同型。 -/
noncomputable def towerStageToPerfect (n : ℕ) : TowerStage A t p n →ₐ[A] C :=
  Ideal.Quotient.liftₐ (towerRel A t p n) (aeval (perfectRoot A C t p n))
    (relIdeal_apply_eq_zero t (p ^ n) _ fun i ↦ by
      rw [aeval_X]
      exact perfectRoot_pow A C t p n i)

/-- 段の変数は指定した根に写る。 -/
@[simp] theorem towerStageToPerfect_mk_X (n : ℕ) (i : Fin h) :
    towerStageToPerfect A C t p n (Ideal.Quotient.mk (towerRel A t p n) (X i)) =
      perfectRoot A C t p n i := by
  change aeval (perfectRoot A C t p n) (X i) = _
  rw [aeval_X]

/-- 標数 `p` の有限段では、任意の元の `pⁿ` 乗が基底環から来る。
多項式の和と変数による積に関する帰納法で、定義関係式から直接示す。 -/
theorem towerStage_pow_mem_range (n : ℕ) [CharP (TowerStage A t p n) p]
    (x : TowerStage A t p n) :
    ∃ a : A, algebraMap A (TowerStage A t p n) a = x ^ (p ^ n) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨a ^ (p ^ n), by rw [map_pow]; rfl⟩
  | add f g hf hg =>
    obtain ⟨a, ha⟩ := hf
    obtain ⟨b, hb⟩ := hg
    exact ⟨a + b, by rw [map_add, ha, hb, map_add, add_pow_char_pow]⟩
  | mul_X f i hf =>
    obtain ⟨a, ha⟩ := hf
    exact ⟨a * t i, by rw [map_mul, ha, map_mul, mul_pow, mk_X_pow]⟩

/-- 塔の各元は、基底環の元のある `p` 冪根である。
元を一つの有限段に降ろし、その段の Frobenius の公式を使う。 -/
theorem tower_pow_mem_range (hchar : ∀ n, CharP (TowerStage A t p n) p)
    (x : Tower A t p) :
    ∃ n : ℕ, ∃ a : A, algebraMap A (Tower A t p) a = x ^ (p ^ n) := by
  obtain ⟨n, y, rfl⟩ := exists_towerOf A t p x
  let := hchar n
  obtain ⟨a, ha⟩ := towerStage_pow_mem_range A t p n y
  refine ⟨n, a, ?_⟩
  rw [IsScalarTower.algebraMap_apply A (TowerStage A t p n) (Tower A t p), ha, map_pow]
  rfl

/-- 有限段が被約で、基底環の像が単射なら、完全環への標準写像も単射。
核の元の `pⁿ` 乗を基底環に戻し、被約性で元自身が零であることを示す。 -/
theorem towerStageToPerfect_injective (n : ℕ)
    [CharP (TowerStage A t p n) p] [IsReduced (TowerStage A t p n)]
    (hinj : Function.Injective (algebraMap A C)) :
    Function.Injective (towerStageToPerfect A C t p n) := by
  apply (injective_iff_map_eq_zero (towerStageToPerfect A C t p n)).mpr
  intro x hx
  obtain ⟨a, ha⟩ := towerStage_pow_mem_range A t p n x
  have hzero : algebraMap A C a = 0 := by
    rw [← (towerStageToPerfect A C t p n).commutes a, ha, map_pow, hx,
      zero_pow (pow_pos (Fact.out : p.Prime).pos n).ne']
  have ha0 : a = 0 := hinj (hzero.trans (map_zero _).symm)
  exact IsReduced.eq_zero x ⟨p ^ n, by rw [← ha, ha0, map_zero]⟩

/-- 各段からの写像は遷移写像と両立する。 -/
theorem towerStageToPerfect_compatible (a b : ℕ) (hab : a ≤ b)
    (x : TowerStage A t p a) :
    towerStageToPerfect A C t p b (towerMap A t p a b hab x) =
      towerStageToPerfect A C t p a x := by
  have heq : (towerStageToPerfect A C t p b).comp (towerMap A t p a b hab) =
      towerStageToPerfect A C t p a := by
    apply Ideal.Quotient.algHom_ext A
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    rw [towerMap_mk_X, map_pow, towerStageToPerfect_mk_X, towerStageToPerfect_mk_X]
    exact perfectRoot_compatible A C t p a b hab i
  exact AlgHom.congr_fun heq x

/-- 塔全体から完全環への標準環準同型。 -/
noncomputable def towerToPerfectRingHom : Tower A t p →+* C :=
  Ring.DirectLimit.lift _ _ C (fun n ↦ (towerStageToPerfect A C t p n).toRingHom)
    (towerStageToPerfect_compatible A C t p)

/-- 標準写像を各段に制限すると、根による写像に戻る。 -/
@[simp] theorem towerToPerfectRingHom_of (n : ℕ) (x : TowerStage A t p n) :
    towerToPerfectRingHom A C t p (towerOf A t p n x) =
      towerStageToPerfect A C t p n x := by
  exact Ring.DirectLimit.lift_of ..

/-- 塔から完全環への写像は基底 `A` の作用を保つ。 -/
noncomputable def towerToPerfect : Tower A t p →ₐ[A] C where
  __ := towerToPerfectRingHom A C t p
  commutes' x := by
    change towerToPerfectRingHom A C t p (algebraMap A (Tower A t p) x) = _
    rw [algebraMap_tower_apply, towerToPerfectRingHom_of, AlgHom.commutes]

/-- 塔からの代数準同型を一つの段に制限したときの計算規則。 -/
@[simp] theorem towerToPerfect_of (n : ℕ) (x : TowerStage A t p n) :
    towerToPerfect A C t p (towerOf A t p n x) = towerStageToPerfect A C t p n x := by
  exact towerToPerfectRingHom_of A C t p n x

/-- 各有限段が被約なら、基底環を単射に含む完全環への塔全体の写像も単射。
任意の核の元を有限段に降ろし、その段での単射性を適用する。 -/
theorem towerToPerfect_injective
    (hchar : ∀ n, CharP (TowerStage A t p n) p)
    (hred : ∀ n, IsReduced (TowerStage A t p n))
    (hinj : Function.Injective (algebraMap A C)) :
    Function.Injective (towerToPerfect A C t p) := by
  apply (injective_iff_map_eq_zero (towerToPerfect A C t p)).mpr
  intro x hx
  obtain ⟨n, y, rfl⟩ := exists_towerOf A t p x
  rw [towerToPerfect_of] at hx
  let := hchar n
  let := hred n
  have hy : y = 0 := towerStageToPerfect_injective A C t p n hinj
    (hx.trans (map_zero _).symm)
  rw [hy, map_zero]

/-- 各段から完全環への基底を保つ写像は、根の一意性によって一意である。 -/
theorem towerStageToPerfect_unique (n : ℕ) (f : TowerStage A t p n →ₐ[A] C) :
    f = towerStageToPerfect A C t p n := by
  apply Ideal.Quotient.algHom_ext A
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, towerStageToPerfect_mk_X]
  apply (iterateFrobeniusEquiv C p n).injective
  change f (Ideal.Quotient.mk (towerRel A t p n) (X i)) ^ (p ^ n) =
    perfectRoot A C t p n i ^ (p ^ n)
  rw [← map_pow, mk_X_pow, AlgHom.commutes, perfectRoot_pow]

/-- 塔全体から完全環への基底を保つ写像も一意である。 -/
theorem towerToPerfect_unique (f : Tower A t p →ₐ[A] C) :
    f = towerToPerfect A C t p := by
  apply AlgHom.ext
  intro x
  obtain ⟨n, y, rfl⟩ := exists_towerOf A t p x
  let g : TowerStage A t p n →ₐ[A] Tower A t p :=
    { towerOf A t p n with
      commutes' := fun a ↦ (IsScalarTower.algebraMap_apply A (TowerStage A t p n)
        (Tower A t p) a).symm }
  have heq := AlgHom.congr_fun (towerStageToPerfect_unique A C t p n (f.comp g)) y
  exact heq.trans (towerToPerfectRingHom_of A C t p n y).symm

end SerrePositivity.Section2
