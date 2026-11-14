module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Delta.DividedPower.RegularSequence.RegularSequencePD
public import SerrePositivity.BhattScholze.Delta.DividedPower.PDivision.PDivision

/-!
# 分冪表示と階乗部分環

## 概要
表示環が p 正則なら、p を反転した環の階乗部分環と同型（BS 著者版 Lemma 2.38）。

## 方針
標準評価射の核を p 反転で消し、全射性は階乗生成元の像から示す。

## 規約
係数は p 局所。階乗部分環の分冪は p 局所化から制限する。

## 使われ方
正則列の分冪包と生の Frobenius 除算の比較。
-/

public noncomputable section

universe u v

open scoped Classical

namespace SerrePositivity.BhattScholze

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
  (a : σ → A) (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))

local notation "P" => DPFamilyPresentation a
local notation "FSub" => pDivisionFactorialSubring p a
local notation "J" => pDivisionFactorialIdeal p a

local instance : CommRing P := Ideal.Quotient.commRing (dpFamilyRelationIdeal a)

local instance : Algebra A FSub := (pDivisionFactorialBase p a).toAlgebra


local notation "L" => Localization.Away (p : A)

private theorem factorialDpow_closed :
    letI := DeltaStructure.primeDividedPowersAwayRatAlgebra hlocal
    let H := DividedPowers.RatAlgebra.dividedPowers (⊤ : Ideal L)
    ∀ (n : ℕ) {x : FSub}, x ∈ J → ∃ y : FSub, (n ≠ 0 → y ∈ J) ∧
      (y : L) = H.dpow n (x : L) := by
  letI := DeltaStructure.primeDividedPowersAwayRatAlgebra hlocal
  let H := DividedPowers.RatAlgebra.dividedPowers (⊤ : Ideal L)
  suffices h : ∀ x ∈ J, ∀ n : ℕ, ∃ y : FSub, (n ≠ 0 → y ∈ J) ∧
      (y : L) = H.dpow n (x : L) by
    exact fun n x hx => h x hx n
  intro x hx
  unfold pDivisionFactorialIdeal at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨⟨s, k⟩, rfl⟩ := hx
      intro n
      let y : FSub := ⟨pDivisionFactorialValue p a s (n * (k+1)),
        pDivisionFactorialSubring_value_mem a s _⟩
      have hγ (m : ℕ) :
          H.dpow m (algebraMap A L (a s)) = pDivisionFactorialValue p a s m :=
        DividedPowers.RatAlgebra.dpow_eq_of_mem _ Submodule.mem_top
      refine ⟨(Nat.uniformBell n (k+1) : FSub) * y, ?_, ?_⟩
      · intro hn
        apply (J).mul_mem_left
        obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (mul_ne_zero hn (Nat.succ_ne_zero k))
        change y ∈ J
        unfold pDivisionFactorialIdeal
        apply Ideal.subset_span
        exact ⟨(s, m), Subtype.ext (by
          change pDivisionFactorialValue p a s (m+1) = pDivisionFactorialValue p a s (n * (k+1))
          exact congrArg (pDivisionFactorialValue p a s) hm.symm)⟩
      · change (Nat.uniformBell n (k+1) : L) * pDivisionFactorialValue p a s (n*(k+1)) =
          H.dpow n (pDivisionFactorialValue p a s (k+1))
        rw [← hγ (k+1), H.dpow_comp (Nat.succ_ne_zero k) Submodule.mem_top, hγ (n*(k+1))]
  | zero =>
      intro n
      by_cases hn : n = 0
      · subst n
        exact ⟨1, by simp, (H.dpow_zero (x := (0 : L)) Submodule.mem_top).symm⟩
      · exact ⟨0, fun _ => (J).zero_mem, (H.dpow_eval_zero hn).symm⟩
  | add x y _ _ hx hy =>
      intro n
      choose u hu hu' using hx
      choose v hv hv' using hy
      refine ⟨∑ k ∈ Finset.antidiagonal n, u k.1 * v k.2, ?_, ?_⟩
      · intro hn
        apply (J).sum_mem
        intro k hk
        by_cases hk₁ : k.1 = 0
        · apply (J).mul_mem_left
          apply hv
          intro hk₂
          exact hn (by simpa [hk₁, hk₂] using (Finset.mem_antidiagonal.mp hk).symm)
        · exact (J).mul_mem_right _ (hu _ hk₁)
      · change (FSub).subtype _ = H.dpow n ((x : L) + (y : L))
        rw [map_sum, H.dpow_add Submodule.mem_top Submodule.mem_top]
        exact Finset.sum_congr rfl fun k _ => by
          rw [map_mul]
          change (u k.1 : L) * (v k.2 : L) = _
          rw [hu', hv']
  | smul b x _ hx =>
      intro n
      obtain ⟨y, hy, hy'⟩ := hx n
      refine ⟨b ^ n * y, fun hn => (J).mul_mem_left _ (hy hn), ?_⟩
      change (b : L) ^ n * (y : L) = H.dpow n ((b : L) * (x : L))
      rw [hy', H.dpow_mul Submodule.mem_top]

/-- 概要：正次数の階乗生成イデアル上の分冪構造。
方針：p 局所化の階乗分冪を制限し、イデアルの生成元で閉性を示す。
規約：係数環の δ 構造を仮定しない（BS 著者版 Lemma 2.38）。
使われ方：正則列の分冪包の標準評価。 -/
def dpFamilyFactorialDividedPowers : DividedPowers J := by
  letI := DeltaStructure.primeDividedPowersAwayRatAlgebra hlocal
  let K := (J).map (FSub).subtype
  apply DividedPowers.ofInjective J K (FSub).subtype Subtype.val_injective
    (DividedPowers.RatAlgebra.dividedPowers K) rfl
  intro n x hx
  obtain ⟨y, hy, hy'⟩ := factorialDpow_closed a hlocal n hx
  refine ⟨y, hy, hy'.trans ?_⟩
  exact (DividedPowers.RatAlgebra.dpow_eq_of_mem _ Submodule.mem_top).trans
    (DividedPowers.RatAlgebra.dpow_eq_of_mem _ (Ideal.mem_map_of_mem (FSub).subtype hx)).symm

/-- 概要：分冪表示から階乗部分環への標準射。
方針：階乗部分環の分冪構造へ表示の普遍射を適用する。
規約：BS 著者版 Lemma 2.38 の標準評価射。
使われ方：p 正則性が得られたときの比較同型。 -/
def dpFamilyToFactorial : P →ₐ[A] FSub :=
  dpFamilyEval a (dpFamilyFactorialDividedPowers a hlocal) (pDivisionFactorialBase_mem_factorialIdeal a)

/-- 概要：各分冪変数の像は対応する階乗値。
方針：標準評価射と階乗部分環の分冪の計算を合わせる。
規約：BS 著者版 Lemma 2.38。
使われ方：比較射の全射性。 -/
theorem dpFamilyToFactorial_generator (s : σ) (n : ℕ) :
    (dpFamilyToFactorial a hlocal (dpFamilyGenerator a s n) :
      Localization.Away (p : A)) = pDivisionFactorialValue p a s n := by
  unfold dpFamilyToFactorial
  rw [dpFamilyEval_generator]
  let H := dpFamilyFactorialDividedPowers a hlocal
  have h := H.factorial_mul_dpow_eq_pow (pDivisionFactorialBase_mem_factorialIdeal a s) (n := n)
  apply (DeltaStructure.primeDividedPowersAwayNat_isUnit hlocal n.factorial
    (Nat.factorial_ne_zero n)).mul_left_cancel
  rw [pDivisionFactorialValue, Ring.mul_inverse_cancel_left _ _
    (DeltaStructure.primeDividedPowersAwayNat_isUnit hlocal n.factorial (Nat.factorial_ne_zero n))]
  exact congrArg (fun x : FSub => (x : L)) h

/-- 概要：標準評価は階乗部分環への全射。
方針：係数と各階乗値を表示環の生成元で持ち上げる。
規約：BS 著者版 Lemma 2.38。
使われ方：比較同型。 -/
theorem dpFamilyToFactorial_surjective : Function.Surjective (dpFamilyToFactorial a hlocal) := by
  let F := dpFamilyToFactorial a hlocal
  have hle : FSub ≤ ((FSub).subtype.comp F.toRingHom).range := by
    apply Subring.closure_le.mpr
    rintro t (⟨b, rfl⟩ | ⟨⟨s, n⟩, rfl⟩)
    · exact ⟨algebraMap A P b, congrArg Subtype.val (F.commutes b)⟩
    · exact ⟨dpFamilyGenerator a s n, dpFamilyToFactorial_generator a hlocal s n⟩
  intro b
  obtain ⟨x, hx⟩ := hle b.property
  exact ⟨x, Subtype.ext hx⟩

private theorem dpFamilyToFactorial_comp_away :
    let Lout := Localization.Away (p : P)
    ∃ g : Localization.Away (p : A) →+* Lout,
      g.comp ((FSub).subtype.comp (dpFamilyToFactorial a hlocal).toRingHom) = algebraMap P Lout := by
  let Lout := Localization.Away (p : P)
  have hpL : IsUnit (algebraMap A Lout (p : A)) := by
    have hp := IsLocalization.Away.algebraMap_isUnit (S := Lout) (p : P)
    simpa only [map_natCast] using hp
  let g : Localization.Away (p : A) →+* Lout := IsLocalization.Away.lift (p : A) hpL
  let F : P →ₐ[A] Lout :=
    { toRingHom := g.comp ((FSub).subtype.comp (dpFamilyToFactorial a hlocal).toRingHom)
      commutes' := by
        intro b
        change g ((dpFamilyToFactorial a hlocal (algebraMap A P b) : FSub) :
          Localization.Away (p : A)) = _
        rw [AlgHom.commutes]
        exact IsLocalization.Away.lift_eq (p : A) hpL b }
  let q : P →ₐ[A] Lout := IsScalarTower.toAlgHom A P Lout
  have hP : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : P) := by
    intro m hm
    simpa only [map_natCast] using (hlocal m hm).map (algebraMap A P)
  have h : F = q := by
    apply dpFamilyHom_ext a
    intro s n
    apply (DeltaStructure.primeDividedPowersAwayNat_isUnit hP n.factorial
      (Nat.factorial_ne_zero n)).mul_left_cancel
    have h : (n.factorial : P) * dpFamilyGenerator a s n = (algebraMap A P (a s)) ^ n :=
      dpFamilyGenerator_factorial_mul a s n
    have hF := congrArg F h
    have hq := congrArg q h
    simp only [map_mul, map_natCast, map_pow, AlgHom.commutes] at hF hq
    exact hF.trans hq.symm
  exact ⟨g, congrArg AlgHom.toRingHom h⟩

/-- 概要：p 正則な分冪表示と階乗部分環の標準同型。
方針：評価は全射で、p 反転したとき通常の局所化単位を経由する。
規約：BS 著者版 Lemma 2.38 の表示比較。
使われ方：任意の分冪標的への普遍性と Corollary 2.39。 -/
def dpFamilyFactorialEquiv (hp : IsRegular (p : P)) : P ≃ₐ[A] FSub := by
  refine AlgEquiv.ofBijective (dpFamilyToFactorial a hlocal)
    ⟨?_, dpFamilyToFactorial_surjective a hlocal⟩
  have hi : Function.Injective (algebraMap P (Localization.Away (p : P))) := by
    apply (IsLocalization.injective_iff_isRegular (Submonoid.powers (p : P))
      (S := Localization.Away (p : P))).mpr
    rintro ⟨x, ⟨i, hi⟩⟩
    exact hi ▸ hp.pow i
  obtain ⟨g, hg⟩ := dpFamilyToFactorial_comp_away a hlocal
  intro x y h
  apply hi
  rw [← hg]
  exact congrArg (fun t : FSub => g t) h


variable {B : Type*} [CommRing B] [Algebra A B] {I : Ideal B}

/-- 概要：p 正則な表示の階乗部分環は、p ねじれを許す任意の分冪標的への普遍性を持つ。
方針：表示からの評価射を移し、正次数の各階乗値上で分冪と可換することを調べる。
規約：BS 著者版 Lemma 2.38 の分冪包。標的は任意の A 分冪代数。
使われ方：正則列の分冪包の底変換と結晶サイト。 -/
theorem existsUnique_dpFamilyFactorialDPMorphism (hp : IsRegular (p : P))
    (H : DividedPowers I) (ha : ∀ s, algebraMap A B (a s) ∈ I) :
    ∃! F : FSub →+* B,
      F.comp (pDivisionFactorialBase p a) = algebraMap A B ∧
        DividedPowers.IsDPMorphism (dpFamilyFactorialDividedPowers a hlocal) H F := by
  let e := dpFamilyFactorialEquiv a hlocal hp
  let F := (dpFamilyEval a H ha).comp e.symm.toAlgHom
  let H₀ := dpFamilyFactorialDividedPowers a hlocal
  let γ := fun s n => (⟨pDivisionFactorialValue p a s n,
    pDivisionFactorialSubring_value_mem a s n⟩ : FSub)
  have he (s : σ) (n : ℕ) : e (dpFamilyGenerator a s n) = γ s n :=
    Subtype.ext (dpFamilyToFactorial_generator a hlocal s n)
  have hγ (s : σ) (n : ℕ) : H₀.dpow n (pDivisionFactorialBase p a (a s)) = γ s n := by
    apply Subtype.ext
    change ((dpFamilyFactorialDividedPowers a hlocal).dpow n
      (algebraMap A FSub (a s)) : L) = pDivisionFactorialValue p a s n
    simpa only [dpFamilyToFactorial, dpFamilyEval_generator] using dpFamilyToFactorial_generator a hlocal s n
  have hF (s : σ) (n : ℕ) : F (γ s n) = H.dpow n (algebraMap A B (a s)) := by
    rw [← he]
    change dpFamilyEval a H ha (e.symm (e (dpFamilyGenerator a s n))) = _
    rw [AlgEquiv.symm_apply_apply, dpFamilyEval_generator]
  have hbase : F.toRingHom.comp (pDivisionFactorialBase p a) = algebraMap A B := by
    apply RingHom.ext
    exact F.commutes
  refine ⟨F.toRingHom, ⟨hbase, ?_⟩, ?_⟩
  · apply DividedPowers.IsDPMorphism.on_span H₀ H
      (S := Set.range (fun t : σ × ℕ => γ t.1 (t.2+1))) rfl
    · rintro _ ⟨⟨s,n⟩, rfl⟩
      change F (γ s (n+1)) ∈ I
      rw [hF]
      exact H.dpow_mem (Nat.succ_ne_zero n) (ha s)
    · rintro k _ ⟨⟨s,n⟩, rfl⟩
      change F (H₀.dpow k (γ s (n+1))) = H.dpow k (F (γ s (n+1)))
      conv_lhs => rw [← hγ]
      rw [H₀.dpow_comp (Nat.succ_ne_zero n) (pDivisionFactorialBase_mem_factorialIdeal a s),
        hγ, map_mul, map_natCast, hF, hF, H.dpow_comp (Nat.succ_ne_zero n) (ha s)]
  · intro g hg
    apply pDivisionFactorialHom_ext a
    · intro b
      exact (DFunLike.congr_fun hg.1 b).trans (F.commutes b).symm
    · intro s n
      change g (γ s n) = F (γ s n)
      rw [hF, ← hγ, ← hg.2.dpow_comp _ (pDivisionFactorialBase_mem_factorialIdeal a s)]
      exact congrArg (H.dpow n) (DFunLike.congr_fun hg.1 (a s))

end SerrePositivity.BhattScholze

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Lemma 2.38"] _root_.SerrePositivity.BhattScholze.dpFamilyFactorialEquiv
