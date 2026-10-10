module

public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Ideal.GoingUp

/-!
# 有限加群とイデアル進完備性

完備な環上の有限加群の完備性、および比較可能なイデアルの冪による完備性の移行を扱う。
§2 の塔の各段の完備性に用いる一般論であり、塔や正規化長さの定義には依存しない。
-/

public section

namespace SerrePositivity

open Submodule
open scoped BigOperators

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- 線形写像はイデアルの冪に関する合同を保存する。 -/
lemma smodEq_map_pow {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) {n : ℕ} {x y : M}
    (h : x ≡ y [SMOD (I ^ n • ⊤ : Submodule R M)]) :
    f x ≡ f y [SMOD (I ^ n • ⊤ : Submodule R N)] :=
  (h.map f).mono (by rw [Submodule.map_le_iff_le_comap]; exact smul_top_le_comap_smul_top _ f)

/-- 前完備な環の有限直積は、加群として前完備である。各座標で極限を取り、有限和で戻す。 -/
theorem isPrecomplete_pi [IsPrecomplete I R] (ι : Type*) [Finite ι] :
    IsPrecomplete I (ι → R) where
  prec' f hf := by
    classical
    let := Fintype.ofFinite ι
    have hc (i : ι) : ∃ L : R, ∀ n,
        f n i ≡ L [SMOD (I ^ n • ⊤ : Ideal R)] := by
      apply IsPrecomplete.prec' (I := I) (fun n ↦ f n i)
      intro m n hmn
      exact smodEq_map_pow I (LinearMap.proj i) (hf hmn)
    choose L hL using hc
    refine ⟨L, fun n ↦ ?_⟩
    have hsum := SModEq.sum (s := Finset.univ) (fun i _ ↦
      smodEq_map_pow I (LinearMap.single R (fun _ : ι ↦ R) i) (hL i n))
    have heq (v : ι → R) : (∑ i, Pi.single i (v i)) = v := by
      ext j
      simp
    simpa only [LinearMap.single_apply, heq] using hsum

/-- 前完備性は全射線形写像で移る。Mathlib の完備化の全射性と自然性を使う。 -/
theorem isPrecomplete_of_surjective {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [IsPrecomplete I M]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) : IsPrecomplete I N := by
  apply (AdicCompletion.of_surjective_iff (I := I) (M := N)).mp
  intro y
  obtain ⟨x, hx⟩ := AdicCompletion.map_surjective_of_mkQ_comp_surjective
    (I := I) (f := f) ((Submodule.mkQ_surjective _).comp hf) y
  obtain ⟨z, hz⟩ := AdicCompletion.of_surjective I M x
  refine ⟨f z, ?_⟩
  rw [← AdicCompletion.map_of, hz, hx]

/-- 前完備な環上の有限生成加群は前完備である。ネーター性は不要。 -/
theorem isPrecomplete_finite [IsPrecomplete I R] (M : Type*) [AddCommGroup M]
    [Module R M] [Module.Finite R M] : IsPrecomplete I M := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  let := isPrecomplete_pi I (Fin n)
  exact isPrecomplete_of_surjective I f hf

/-- 完備ネーター局所環上の有限生成加群は極大イデアル進完備である。
分離性には Mathlib の Krull の共通部分定理を用いる。 -/
theorem isAdicComplete_finite [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsAdicComplete (IsLocalRing.maximalIdeal R) M := by
  let := isPrecomplete_finite (IsLocalRing.maximalIdeal R) M
  exact ⟨⟩

/-- `I ≤ J` かつ `J` のある冪が `I` に含まれるとき、`I` 進完備性は `J` 進完備性に移る。
合同列の部分列を取り、イデアルの冪の共終性を直接使う。 -/
theorem isAdicComplete_of_pow_le (J : Ideal R) (hIJ : I ≤ J)
    (k : ℕ) (hk : J ^ k ≤ I) (M : Type*) [AddCommGroup M] [Module R M]
    [IsAdicComplete I M] : IsAdicComplete J M := by
  have hpow (n : ℕ) : J ^ ((k + 1) * n) ≤ I ^ n := by
    rw [pow_mul]
    exact pow_le_pow_left' ((Ideal.pow_le_pow_right (Nat.le_succ k)).trans hk) n
  have hmono (n : ℕ) : n ≤ (k + 1) * n := Nat.le_mul_of_pos_left n (Nat.succ_pos k)
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    apply IsHausdorff.haus (inferInstance : IsHausdorff I M) x
    intro n
    exact (hx ((k + 1) * n)).mono (smul_mono_left (hpow n))
  · intro f hf
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) (fun n ↦ f ((k + 1) * n))
      (fun {m n} hmn ↦ (hf (Nat.mul_le_mul_left _ hmn)).mono
        (smul_mono_left (hpow m)))
    refine ⟨L, fun n ↦ (hf (hmono n)).trans ?_⟩
    exact (hL n).mono (smul_mono_left (pow_le_pow_left' hIJ n))

/-- ネーター環では、`I ≤ J ≤ √I` なら `I` 進完備性から `J` 進完備性が従う。 -/
theorem isAdicComplete_of_le_radical [IsNoetherianRing R] (J : Ideal R)
    (hIJ : I ≤ J) (hJI : J ≤ I.radical) (M : Type*) [AddCommGroup M] [Module R M]
    [IsAdicComplete I M] : IsAdicComplete J M := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hJI (IsNoetherian.noetherian J)
  exact isAdicComplete_of_pow_le I J hIJ k hk M

/-- 整拡大で両環が局所環なら、拡大した極大イデアルの根基は拡大環の極大イデアルである。
極大イデアルの収縮と、極大イデアルの上の素イデアルが極大であることを使う。 -/
theorem radical_map_maximalIdeal_of_integral [IsLocalRing R]
    (S : Type*) [CommRing S] [IsLocalRing S] [Algebra R S] [Algebra.IsIntegral R S] :
    ((IsLocalRing.maximalIdeal R).map (algebraMap R S)).radical =
      IsLocalRing.maximalIdeal S := by
  have hint : (algebraMap R S).IsIntegral := fun x ↦ Algebra.IsIntegral.isIntegral x
  have hcomax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
    (algebraMap R S) hint (IsLocalRing.maximalIdeal S)
  have hle : (IsLocalRing.maximalIdeal R).map (algebraMap R S) ≤
      IsLocalRing.maximalIdeal S := by
    rw [Ideal.map_le_iff_le_comap, IsLocalRing.eq_maximalIdeal hcomax]
  apply le_antisymm
  · simpa only [Ideal.IsPrime.radical
      (inferInstance : (IsLocalRing.maximalIdeal S).IsPrime)] using Ideal.radical_mono hle
  · rw [Ideal.radical_eq_sInf]
    apply le_sInf
    rintro P ⟨hP, hprime⟩
    let := hprime
    have heq : P.comap (algebraMap R S) = IsLocalRing.maximalIdeal R := by
      apply le_antisymm
      · exact IsLocalRing.le_maximalIdeal (Ideal.comap_ne_top _ hprime.ne_top)
      · exact Ideal.map_le_iff_le_comap.mp hP
    have hmax : (P.comap (algebraMap R S)).IsMaximal := by
      rw [heq]
      infer_instance
    rw [IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ hint P hmax)]

/-- 完備ネーター局所環の有限な局所環拡大は、その極大イデアルに関して完備である。
有限加群の完備性を係数拡大したイデアルへ移し、根基の一致から冪を比較する。
環準同型の単射性や、剰余体の一致は必要ない。 -/
theorem isAdicComplete_finite_local_algebra [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (S : Type*) [CommRing S] [IsLocalRing S] [Algebra R S] [Module.Finite R S] :
    IsAdicComplete (IsLocalRing.maximalIdeal S) S := by
  let := isAdicComplete_finite (R := R) S
  let : IsNoetherianRing S := isNoetherian_of_tower R inferInstance
  let : IsAdicComplete ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) S :=
    (IsAdicComplete.map_algebraMap_iff _ _).mpr inferInstance
  have hrad := radical_map_maximalIdeal_of_integral (R := R) S
  exact isAdicComplete_of_le_radical _ _ (hrad ▸ Ideal.le_radical) hrad.ge S

end SerrePositivity
