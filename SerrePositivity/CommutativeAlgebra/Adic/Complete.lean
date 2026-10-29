module

public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.LinearAlgebra.Quotient.Basic
public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Exact
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.AdicCompletion.Topology

/-! # 古典的なイデアル進完備性の移行

概要：`IsAdicComplete I M`（分離かつ前完備）を、次の操作に沿って移す。
- 線形写像：全射は前完備性を、単射は分離性を移す。線形同値は完備性を保つ。分離加群への写像の核による商は完備。
- 直積：有限個の前完備・完備な加群の直積。
- 有限性：完備 Noether 局所環上の有限加群は、極大イデアル進・より小さい準素イデアル進でも完備。
- イデアルの取り替え：`I ≤ J`、`J^k ≤ I` や根基の一致、閉じた冪部分加群、二つのイデアルの和（各商が完備なら和でも完備）。
- 一様なフィルトレーション比較を持つ写像の像による商、分離環への写像の像。
方針：前完備性は Mathlib の `AdicCompletion.of_surjective_iff` と `map_surjective_of_mkQ_comp_surjective`、
分離性は `I^n` 倍の合同の像を追う。有限加群は Mathlib の `IsHausdorff (maximalIdeal R) M` を使う。
規約：完備性はすべて古典的（Mathlib の `IsAdicComplete`）。導来完備性は扱わない。
使われ方：冪級数環の完備性、完備微分、Witt 正規化、Bhatt–Scholze 側。Mathlib への提出候補。
-/

@[expose] public noncomputable section

universe u v w

namespace SerrePositivity

section AdicCompleteness

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
theorem isPrecomplete_pi {M : Type*} [AddCommGroup M] [Module R M] [IsPrecomplete I M]
    (ι : Type*) [Finite ι] : IsPrecomplete I (ι → M) where
  prec' f hf := by
    classical
    let := Fintype.ofFinite ι
    have hc (i : ι) : ∃ L : M, ∀ n,
        f n i ≡ L [SMOD (I ^ n • ⊤ : Submodule R M)] := by
      apply IsPrecomplete.prec' (I := I) (fun n ↦ f n i)
      intro m n hmn
      exact smodEq_map_pow I (LinearMap.proj i) (hf hmn)
    choose L hL using hc
    refine ⟨L, fun n ↦ ?_⟩
    have hsum := SModEq.sum (s := Finset.univ) (fun i _ ↦
      smodEq_map_pow I (LinearMap.single R (fun _ : ι ↦ M) i) (hL i n))
    have heq (v : ι → M) : (∑ i, Pi.single i (v i)) = v := by
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
  let := isPrecomplete_pi (M := R) I (Fin n)
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

end AdicCompleteness

section AdicModuleProducts

/-- 完備加群の有限直積も完備。イデアルの有限生成性・Noether性は不要。 -/
theorem isAdicComplete_function {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Finite ι] (I : Ideal R) [IsAdicComplete I M] : IsAdicComplete I (ι → M) := by
  classical
  let := Fintype.ofFinite ι
  let E := (AdicCompletion.piEquivOfFintype I (fun _ : ι ↦ M)).restrictScalars R
  have hof (f : ι → M) : E (AdicCompletion.of I (ι → M) f) =
      fun i ↦ AdicCompletion.of I M (f i) := by
    funext i
    simp [E, AdicCompletion.pi, AdicCompletion.map_of]
  apply AdicCompletion.of_bijective_iff.mp
  constructor
  · intro f g h
    have he := congrArg E h
    rw [hof, hof] at he
    funext i
    exact AdicCompletion.of_injective I M (congrFun he i)
  · intro x
    let f : ι → M := fun i ↦ (AdicCompletion.ofLinearEquiv I M).symm (E x i)
    refine ⟨f, E.injective ?_⟩
    rw [hof]
    funext i
    exact AdicCompletion.of_ofLinearEquiv_symm I (M := M) (E x i)

end AdicModuleProducts

section AdicCompletenessClosedQuotient

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- 各I冪商がJ進分離なら、J進完備性は小さいイデアルIへ移る。
Noether性・有限性は冪商の分離性の供給側だけで使う。 -/
theorem isAdicComplete_of_le_of_hausdorff_quotients
    (I J : Ideal R) (hIJ : I ≤ J) [IsAdicComplete J M]
    [∀ n : ℕ, IsHausdorff J (M ⧸ (I ^ n • (⊤ : Submodule R M)))] :
    IsAdicComplete I M := by
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    apply IsHausdorff.haus (inferInstance : IsHausdorff J M) x
    intro n
    exact (hx n).mono (Submodule.smul_mono_left (pow_le_pow_left' hIJ n))
  · intro f hf
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := J) f (fun {m n} h ↦
      (hf h).mono (Submodule.smul_mono_left (pow_le_pow_left' hIJ m)))
    refine ⟨L, ?_⟩
    intro i
    let Q := I ^ i • (⊤ : Submodule R M)
    have he : Q.mkQ (f i) = Q.mkQ L := by
      apply (IsHausdorff.eq_iff_smodEq (I := J)).mpr
      intro n
      let k := max i n
      have hfi : Q.mkQ (f i) = Q.mkQ (f k) := by
        exact (Submodule.Quotient.eq _).mpr (SModEq.sub_mem.mp (hf (le_max_left i n)))
      rw [hfi]
      exact (smodEq_map_pow J Q.mkQ (hL k)).mono
        (Submodule.smul_mono_left (Ideal.pow_le_pow_right (le_max_right i n)))
    exact SModEq.sub_mem.mpr ((Submodule.Quotient.eq _).mp he)

/-- 完備Noether局所環上の有限加群は、極大イデアル以下の任意のイデアルについて完備。
極大イデアル進完備性と各冪商のKrull分離性から導く。 -/
theorem isAdicComplete_finite_of_le_maximalIdeal
    [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Module.Finite R M]
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R) : IsAdicComplete I M := by
  let : IsAdicComplete (IsLocalRing.maximalIdeal R) M :=
    isAdicComplete_finite (R := R) M
  exact isAdicComplete_of_le_of_hausdorff_quotients I (IsLocalRing.maximalIdeal R) hI

end AdicCompletenessClosedQuotient

section AdicCompletenessSup

variable {R : Type*} [CommRing R]

/-- I商でのJ冪合同は、元の環でのI+J冪合同に等しい。 -/
theorem smodEq_quotient_iff_sup (I J : Ideal R) (n : ℕ) (x y : R) :
    I.mkQ x ≡ I.mkQ y [SMOD (J ^ n • (⊤ : Submodule R (R ⧸ I)))] ↔
      x ≡ y [SMOD (I ⊔ J ^ n)] := by
  have he : (J ^ n • (⊤ : Submodule R (R ⧸ I))).comap I.mkQ = I ⊔ J ^ n := by
    have hm : Submodule.map I.mkQ (J ^ n : Submodule R R) =
        J ^ n • (⊤ : Submodule R (R ⧸ I)) := by
      have ht : (J ^ n : Submodule R R) = J ^ n • (⊤ : Submodule R R) := by
        simp only [smul_eq_mul, Ideal.mul_top]
      nth_rw 1 [ht]
      rw [Submodule.map_smul'', Submodule.map_top, I.range_mkQ]
    rw [← hm, Submodule.comap_map_mkQ]
  simp only [SModEq.sub_mem, ← map_sub, ← Submodule.mem_comap, he]

/-- I進完備性と全I冪商のJ進完備性から、I+J進完備性を導く。 -/
theorem isAdicComplete_sup_of_complete_quotients (I J : Ideal R)
    [IsAdicComplete I R] [∀ n : ℕ, IsAdicComplete J (R ⧸ I ^ n)] :
    IsAdicComplete (I ⊔ J) R := by
  classical
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    apply IsHausdorff.haus (inferInstance : IsHausdorff I R) x
    intro n
    have hzero : (I ^ n).mkQ x = 0 := by
      apply (IsHausdorff.eq_iff_smodEq (I := J)).mpr
      intro k
      apply (smodEq_quotient_iff_sup (I ^ n) J k x 0).mpr
      have hh := hx (n + k)
      simp only [smul_eq_mul, Ideal.mul_top] at hh
      exact hh.mono Ideal.sup_pow_add_le_pow_sup_pow
    simpa only [smul_eq_mul, Ideal.mul_top] using
      SModEq.sub_mem.mpr ((Submodule.Quotient.eq _).mp hzero)
  · intro f hf
    have hlim (n : ℕ) : ∃ L : R ⧸ I ^ n, ∀ k : ℕ,
        (I ^ n).mkQ (f (n + k)) ≡ L [SMOD (J ^ k • (⊤ : Submodule R (R ⧸ I ^ n)))] := by
      apply IsPrecomplete.prec' (I := J)
      intro a b hab
      apply (smodEq_quotient_iff_sup (I ^ n) J a _ _).mpr
      have hh := hf (Nat.add_le_add_left hab n)
      simp only [smul_eq_mul, Ideal.mul_top] at hh
      exact hh.mono Ideal.sup_pow_add_le_pow_sup_pow
    choose L hL using hlim
    choose r hr using (fun n ↦ (I ^ n).mkQ_surjective (L n))
    have ha (n k : ℕ) : f (n + k) ≡ r n [SMOD (I ^ n ⊔ J ^ k)] := by
      apply (smodEq_quotient_iff_sup (I ^ n) J k _ _).mp
      rw [hr]
      exact hL n k
    have hc : ∀ {n m : ℕ}, n ≤ m → r n ≡ r m [SMOD (I ^ n • ⊤ : Ideal R)] := by
      intro n m hnm
      have hq : (I ^ n).mkQ (r n) = (I ^ n).mkQ (r m) := by
        apply (IsHausdorff.eq_iff_smodEq (I := J)).mpr
        intro k
        apply (smodEq_quotient_iff_sup (I ^ n) J k _ _).mpr
        have h1 := (ha n (m + k)).mono
          (sup_le_sup_left (Ideal.pow_le_pow_right (Nat.le_add_left k m)) _)
        have h2 := (ha m (n + k)).mono
          (sup_le_sup (Ideal.pow_le_pow_right hnm)
            (Ideal.pow_le_pow_right (Nat.le_add_left k n)))
        rw [show m + (n + k) = n + (m + k) by omega] at h2
        exact h1.symm.trans h2
      simpa only [smul_eq_mul, Ideal.mul_top] using
        SModEq.sub_mem.mpr ((Submodule.Quotient.eq _).mp hq)
    obtain ⟨a, ha'⟩ := IsPrecomplete.prec' (I := I) r hc
    refine ⟨a, ?_⟩
    intro n
    have h1 := hf (show n ≤ n + n by omega)
    have h2 := (ha n n).mono
      (sup_le (pow_le_pow_left' le_sup_left n) (pow_le_pow_left' le_sup_right n))
    have h3 : r n ≡ a [SMOD ((I ⊔ J) ^ n • ⊤ : Ideal R)] := (ha' n).mono
      (Submodule.smul_mono_left (pow_le_pow_left' (show I ≤ I ⊔ J from le_sup_left) n))
    simp only [smul_eq_mul, Ideal.mul_top] at h1 h3 ⊢
    exact h1.trans (h2.trans h3)

/-- Noether局所環上の有限加群は、極大イデアル以下の完備イデアルに沿って完備。 -/
theorem isAdicComplete_finite_of_ideal_complete
    [IsNoetherianRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ IsLocalRing.maximalIdeal R) [IsAdicComplete I R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsAdicComplete I M := by
  let : IsPrecomplete I M := isPrecomplete_finite I M
  refine { haus' := ?_ }
  intro x hx
  apply IsHausdorff.haus (inferInstance : IsHausdorff (IsLocalRing.maximalIdeal R) M) x
  intro n
  exact (hx n).mono (Submodule.smul_mono_left (pow_le_pow_left' hI n))

/-- Noether局所環でI進・J進の双方に完備なら、和I+Jについても完備。 -/
theorem isAdicComplete_sup_of_noetherian_local
    [IsNoetherianRing R] [IsLocalRing R] (I J : Ideal R)
    (hJ : J ≤ IsLocalRing.maximalIdeal R) [IsAdicComplete I R] [IsAdicComplete J R] :
    IsAdicComplete (I ⊔ J) R := by
  let : ∀ n : ℕ, IsAdicComplete J (R ⧸ I ^ n) := fun n ↦
    isAdicComplete_finite_of_ideal_complete J hJ (R ⧸ I ^ n)
  exact isAdicComplete_sup_of_complete_quotients I J

end AdicCompletenessSup

section AdicKernelQuotient

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- 分離加群への単射線形写像があれば、定義域も分離している。 -/
theorem isHausdorff_of_injective_linearMap (I : Ideal R) [IsHausdorff I N]
    (f : M →ₗ[R] N) (hf : Function.Injective f) : IsHausdorff I M := by
  refine ⟨fun x hx ↦ hf ?_⟩
  rw [map_zero]
  apply IsHausdorff.haus (inferInstance : IsHausdorff I N) (f x)
  intro n
  simpa only [map_zero] using smodEq_map_pow I f (hx n)

/-- 前完備加群から分離加群への線形写像の核による商は完備。 -/
theorem isAdicComplete_quotient_ker (I : Ideal R) [IsPrecomplete I M]
    [IsHausdorff I N] (f : M →ₗ[R] N) : IsAdicComplete I (M ⧸ LinearMap.ker f) := by
  let k := (LinearMap.ker f).liftQ f le_rfl
  have hk : Function.Injective k := by
    apply LinearMap.ker_eq_bot.mp
    exact Submodule.ker_liftQ_eq_bot _ f le_rfl le_rfl
  let := isHausdorff_of_injective_linearMap I k hk
  let := isPrecomplete_of_surjective I (LinearMap.ker f).mkQ
    (Submodule.mkQ_surjective _)
  exact ⟨⟩

end AdicKernelQuotient

section AdicCompleteLinearEquiv

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {M : Type v} {N : Type w} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

/-- 線形同値は古典的 I 進完備性を保つ。 -/
theorem isAdicComplete_of_linearEquiv (e : M ≃ₗ[R] N) (hM : IsAdicComplete I M) :
    IsAdicComplete I N := by
  have := hM
  have : IsPrecomplete I N := isPrecomplete_of_surjective I e.toLinearMap e.surjective
  have : IsHausdorff I N :=
    isHausdorff_of_injective_linearMap I e.symm.toLinearMap e.symm.injective
  exact {}

end AdicCompleteLinearEquiv

section AdicStrictQuotient

set_option backward.isDefEq.respectTransparency false

variable {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- 完備加群間の写像に一様なフィルトレーション比較があれば、その像による商は完備。 -/
theorem isAdicComplete_quotient_range_of_uniform_filtration_bound
    (I : Ideal R) [IsAdicComplete I M] [IsAdicComplete I N] (f : M →ₗ[R] N)
    (hbound : ∃ k : ℕ, ∀ n : ℕ,
      Submodule.comap f (I ^ (n + k) • (⊤ : Submodule R N)) ≤
        I ^ n • (⊤ : Submodule R M)) : IsAdicComplete I (N ⧸ f.range) := by
  let q := f.range.mkQ
  have hex : Function.Exact f q := by
    rw [LinearMap.exact_iff]
    exact Submodule.ker_mkQ f.range
  have hc := adicCompletion_map_exact_of_uniform_filtration_bound I f q hex
    (Submodule.mkQ_surjective _) hbound
  let := isPrecomplete_of_surjective I q (Submodule.mkQ_surjective _)
  refine { haus' := ?_ }
  intro x hx
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective f.range x
  have hy : AdicCompletion.map I q (AdicCompletion.of I N y) = 0 := by
    rw [AdicCompletion.map_of]
    ext n
    simpa [AdicCompletion.of, SModEq.zero, q] using hx n
  obtain ⟨z, hz⟩ := (hc (AdicCompletion.of I N y)).mp hy
  obtain ⟨w, rfl⟩ := AdicCompletion.of_surjective I M z
  rw [AdicCompletion.map_of] at hz
  have hw : f w = y := (AdicCompletion.of_inj (I := I)).mp hz
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨w, hw⟩

end AdicStrictQuotient

section AdicRingHomRange

/-- The image of a p-adically complete ring in a p-adically separated ring is
p-adically complete, without a finite generation assumption on the kernel. -/
theorem isAdicComplete_ringHom_range {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (p : ℕ) (f : R →+* S)
    [IsAdicComplete (Ideal.span {(p : R)}) R]
    [IsHausdorff (Ideal.span {(p : S)}) S] :
    IsAdicComplete (Ideal.span {(p : f.range)}) f.range := by
  let : Algebra R S := f.toAlgebra
  have hmap : (Ideal.span {(p : R)}).map (algebraMap R S) =
      Ideal.span {(p : S)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  let : IsHausdorff (Ideal.span {(p : R)}) S := by
    exact (IsHausdorff.map_algebraMap_iff (I := Ideal.span {(p : R)}) (S := S) (M := S)).mp
      (by simpa only [hmap] using (inferInstance : IsHausdorff (Ideal.span {(p : S)}) S))
  let : IsAdicComplete (Ideal.span {(p : R)}) (R ⧸ RingHom.ker f) :=
    isAdicComplete_quotient_ker (Ideal.span {(p : R)}) (Algebra.linearMap R S)
  have hQmap : (Ideal.span {(p : R)}).map (algebraMap R (R ⧸ RingHom.ker f)) =
      Ideal.span {(p : R ⧸ RingHom.ker f)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hQ : IsAdicComplete (Ideal.span {(p : R ⧸ RingHom.ker f)})
      (R ⧸ RingHom.ker f) := by
    rw [← hQmap]
    exact (IsAdicComplete.map_algebraMap_iff _ _).mpr inferInstance
  let e := RingHom.quotientKerEquivRange f
  have he := (IsAdicComplete.congr_ringEquiv
    (Ideal.span {(p : R ⧸ RingHom.ker f)}) e).mpr hQ
  simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using he

end AdicRingHomRange

end SerrePositivity
