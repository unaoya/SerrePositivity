module


public meta import SerrePositivity.Util.Citation
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.Ring
public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
public import SerrePositivity.CommutativeAlgebra.Adic.Complete
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Closure
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.KoszulModel
public import SerrePositivity.BhattScholze.Delta.Perfect.DistinguishedRegular

/-!
# 有界 prism の完備性（BS 著者版 Lemma 3.7 (1)）

## 概要
有界 prism の台環は古典的 p 進・(p,d) 進完備で p 進分離。完全 prism の (p,d) 進完備性、正則元の冪商の有界ねじれ。
古典的 p 進完備性は、BS 著者版 Lemma 3.7 (1) の (p,d) 進完備性から取り出す帰結であり、Lemma 4.8 と Remark 7.15 の入力射の構成に使う。

## 方針
導来完備性と分離性から古典的完備性を出す。d の冪商のねじれを帰納的に評価する。

## 規約
向き付き。BS 著者版 Lemma 3.7 の (2)〜(4) は未。

## 使われ方
BS 著者版 Lemma 4.8（Prism/PerfectPrismHomLift）、有界 prism の tilt。旧 Andre/Remark715 から移した。
-/

universe u

/-! ## 正則な生成元の全冪商の有界ねじれ

## 概要

d が正則で B/(d) の a 冪ねじれが a^N で消えるなら、B/(d^m) の a 冪ねじれは
a^(N*m) で消える。BS 著者版 Remark 7.15（著者版 p.62）の有界試験 prism の完備性への入力。

## 方針

a^N x=d y と書き、d の消去で y の一段低い冪商に帰着する。
原典とは異なる主イデアルの可除性による帰納計算。

## 規約

a の正則性・素数性・δ 構造は不要。零冪商と N=0 も含む。

## 使われ方

有界 prism 商の p 冪ねじれを全生成元冪商へ移し、古典的 (p,d) 完備性を得る。
-/

@[expose] public noncomputable section RegularPowerQuotientTorsion

namespace SerrePositivity.BhattScholze
variable {B : Type u} [CommRing B]

/-- 概要：一乗商でのねじれの有界指数 N は m 乗商で N*m となる。
方針：a^N x=d y と書き、d の正則性による消去と m に関する帰納法を使う。
規約：可除性として述べ、係数元 a には制約しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の全冪商における有界ねじれ。 -/
theorem regular_power_quotient_torsion_bound_dvd (a d : B)
    (hd : Function.Injective (fun x : B => d * x)) (N : ℕ)
    (hN : ∀ k : ℕ, ∀ x : B, d ∣ a ^ k * x → d ∣ a ^ N * x)
    (m k : ℕ) (x : B) (hx : d ^ m ∣ a ^ k * x) : d ^ m ∣ a ^ (N * m) * x := by
  induction m generalizing k x with
  | zero => simp
  | succ m ih =>
    have hdx : d ∣ a ^ k * x := (dvd_pow_self d (Nat.succ_ne_zero m)).trans hx
    obtain ⟨y, hy⟩ := hN k x hdx
    obtain ⟨z, hz⟩ := hx
    have hdy : d * (a ^ k * y) = d * (d ^ m * (a ^ N * z)) := by
      calc
        _ = a ^ k * (d * y) := by ring
        _ = a ^ k * (a ^ N * x) := by rw [← hy]
        _ = a ^ N * (a ^ k * x) := by ring
        _ = a ^ N * (d ^ (m + 1) * z) := by rw [hz]
        _ = _ := by rw [pow_succ]; ring
    have hydiv : d ^ m ∣ a ^ k * y := ⟨a ^ N * z, hd hdy⟩
    obtain ⟨w, hw⟩ := ih k y hydiv
    refine ⟨w, ?_⟩
    calc
      a ^ (N * (m + 1)) * x = a ^ (N * m) * (a ^ N * x) := by
        rw [Nat.mul_succ, pow_add]
        ring
      _ = a ^ (N * m) * (d * y) := by rw [hy]
      _ = d * (a ^ (N * m) * y) := by ring
      _ = d * (d ^ m * w) := by rw [hw]
      _ = d ^ (m + 1) * w := by rw [pow_succ]; ring

/-- 概要：正則生成元の m 乗商の a 冪ねじれは、一乗商の有界指数の m 倍で消える。
方針：商での零を主イデアルの可除性に戻し、一般の帰納計算を適用する。
規約：素数性・p 正則性を要求せず、元の実商環を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の有界試験 prism の全冪商の完備性。 -/
theorem regular_power_quotient_torsion_bound (a d : B)
    (hd : Function.Injective (fun x : B => d * x)) (N : ℕ)
    (hN : ∀ k : ℕ, ∀ x : B ⧸ Ideal.span {d},
      (Ideal.Quotient.mk (Ideal.span {d}) a) ^ k * x = 0 →
        (Ideal.Quotient.mk (Ideal.span {d}) a) ^ N * x = 0)
    (m k : ℕ) (x : B ⧸ Ideal.span {d ^ m})
    (hx : (Ideal.Quotient.mk (Ideal.span {d ^ m}) a) ^ k * x = 0) :
    (Ideal.Quotient.mk (Ideal.span {d ^ m}) a) ^ (N * m) * x = 0 := by
  have hNdvd : ∀ k : ℕ, ∀ y : B, d ∣ a ^ k * y → d ∣ a ^ N * y := by
    intro k y hy
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hz := hN k (Ideal.Quotient.mk (Ideal.span {d}) y)
      (by simpa only [map_pow, map_mul] using
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hy))
    simpa only [map_pow, map_mul] using hz
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hy : d ^ m ∣ a ^ k * y := Ideal.mem_span_singleton.mp
    (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [map_pow, map_mul] using hx))
  have hz := _root_.SerrePositivity.BhattScholze.regular_power_quotient_torsion_bound_dvd a d hd N hNdvd m k y hy
  simpa only [map_pow, map_mul] using
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hz)

end SerrePositivity.BhattScholze

end RegularPowerQuotientTorsion

/-! ## 有界試験 prism の共通二元イデアルに沿う古典的完備性

## 概要

prism 商の p 冪ねじれが有界なら、台環は (p,d) に沿って古典的完備となり、p 進分離でもある。
BS 著者版 Remark 7.15（著者版 p.62）の一般の有界試験 prism への根列持上げに用いる。

## 方針

全 d 冪商へねじれの有界性を移し、導来 p 完備性から古典的完備性を得る。
その後 d 完備性と組み合わせる。原典とは異なる有界指数の帰納計算による経路。

## 規約

試験 prism の完全性も、台環・商の p 正則性も要求しない。有界性は明示する。

## 使われ方

共通完備商による互換根列の一意持上げと、根の rank 1 性に必要な分離性を供給する。
-/

@[expose] public noncomputable section BoundedPrismAdicComplete

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.SerrePositivity.DerivedCompletion
variable {B : Type u} [CommRing B] {p : ℕ} [Fact p.Prime]
variable (Q : _root_.SerrePositivity.BhattScholze.OrientedPrism p B)
variable (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
  (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0)

include hB in
/-- 概要：有界 prism の生成元の全冪商は p に沿って古典的完備。
方針：N*m のねじれ評価と商の導来完備性を、有界ねじれによる比較へ渡す。
規約：台環や商の p 正則性は不要で、零冪商も含む。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の有界試験 prism の共通完備性。 -/
theorem boundedPrism_generator_power_quotient_prime_complete (m : ℕ) :
    IsAdicComplete (Ideal.span {(p : B)}) (B ⧸ (Ideal.span {Q.generator}) ^ m) := by
  obtain ⟨N, hN⟩ := hB
  change ∀ n : ℕ, ∀ x : B ⧸ Ideal.span {Q.generator},
    (p : B ⧸ Ideal.span {Q.generator}) ^ n * x = 0 →
      (p : B ⧸ Ideal.span {Q.generator}) ^ N * x = 0 at hN
  rw [Ideal.span_singleton_pow]
  apply (IsAdicComplete.map_algebraMap_iff
    (I := Ideal.span {(p : B)}) (S := B ⧸ Ideal.span {Q.generator ^ m})
    (M := B ⧸ Ideal.span {Q.generator ^ m})).mp
  rw [Ideal.map_span, Set.image_singleton, map_natCast]
  apply (isRingModuleComplete_iff_isAdicComplete_natCast_of_bounded_torsion
    (B ⧸ Ideal.span {Q.generator ^ m}) p ?_).mp
    (isModuleComplete_principal_quotient_natCast B p (Q.generator ^ m) Q.complete_p)
  refine ⟨N * m, fun n x hx => ?_⟩
  have hN' : ∀ n : ℕ, ∀ x : B ⧸ Ideal.span {Q.generator},
      (Ideal.Quotient.mk (Ideal.span {Q.generator}) (p : B)) ^ n * x = 0 →
        (Ideal.Quotient.mk (Ideal.span {Q.generator}) (p : B)) ^ N * x = 0 := by
    intro n x hx
    have hx' : (p : B ⧸ Ideal.span {Q.generator}) ^ n * x = 0 := by
      simpa only [map_natCast] using hx
    simpa only [map_natCast] using hN n x hx'
  simpa only [map_natCast] using
    _root_.SerrePositivity.BhattScholze.regular_power_quotient_torsion_bound (p : B) Q.generator Q.generator_regular N hN' m n x
      (by simpa only [map_natCast] using hx)

include hB in
/-- 概要：有界 prism の台環は (p,d) に沿って古典的完備（BS 著者版 Lemma 3.7 (1) の向き付き prism の場合）。
方針：d 完備性と全 d 冪商の p 完備性から和イデアルの完備性を得る。
規約：prism の完全性や p,d の正則列条件は要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の一般有界試験 prism の共通完備商。 -/
theorem boundedPrism_pair_isAdicComplete :
    IsAdicComplete (Ideal.span {(p : B), Q.generator}) B := by
  let := Q.isAdicComplete_generator
  let : ∀ n : ℕ, IsAdicComplete (Ideal.span {(p : B)})
      (B ⧸ (Ideal.span {Q.generator}) ^ n) :=
    _root_.SerrePositivity.BhattScholze.boundedPrism_generator_power_quotient_prime_complete Q hB
  have he : Ideal.span {Q.generator} ⊔ Ideal.span {(p : B)} =
      Ideal.span {(p : B), Q.generator} := by
    rw [← Ideal.span_union, Set.singleton_union]
    exact Ideal.span_pair_comm
  rw [← he]
  exact _root_.SerrePositivity.isAdicComplete_sup_of_complete_quotients (Ideal.span {Q.generator}) (Ideal.span {(p : B)})

include hB in
/-- 概要：有界 prism の商は p に沿って古典的完備。
方針：商の導来 p 完備性と定義の有界ねじれを比較定理へ供給する。
規約：試験 prism の台環にも商にも p 正則性を要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の共通完備商による根列の持上げ。 -/
theorem boundedPrism_quotient_isAdicComplete_prime :
    IsAdicComplete (Ideal.span {(p : B ⧸ Q.ideal)}) (B ⧸ Q.ideal) :=
  (isRingModuleComplete_iff_isAdicComplete_natCast_of_bounded_torsion
    (B ⧸ Q.ideal) p hB).mp
    (isModuleComplete_principal_quotient_natCast B p Q.generator Q.complete_p)

include hB in
/-- 概要：有界 prism の台環は p 進分離である。
方針：(p)⊆(p,d) の冪合同を共通完備イデアルの分離性へ移す。
規約：古典的 p 完備性や p 正則性は仮定しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の持上げた互換根列の rank 1 判定。 -/
theorem boundedPrism_isHausdorff_prime : IsHausdorff (Ideal.span {(p : B)}) B := by
  let := _root_.SerrePositivity.BhattScholze.boundedPrism_pair_isAdicComplete Q hB
  have hle : Ideal.span {(p : B)} ≤ Ideal.span {(p : B), Q.generator} := by
    apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact Ideal.subset_span (by simp)
  constructor
  intro x hx
  apply IsHausdorff.haus' (I := Ideal.span {(p : B), Q.generator})
  intro n
  exact (hx n).mono (Submodule.smul_mono_left (pow_le_pow_left' hle n))

end SerrePositivity.BhattScholze

end BoundedPrismAdicComplete

/-! ## André A1-a：有界 prism の台環の古典的 p 完備性

## 概要

導来主元完備で主元進分離な環は古典的に完備である。これを有界 prism に適用する。
BS 著者版 Lemma 4.8（著者版 pp.38–39）の基底射の存在と BS 著者版 Remark 7.15（p.62）の入力比較の準備。

## 方針

導来完備性から列の差分作用の全射性を得て前完備性を供給し、既知の分離性と合わせる。
有界 prism では (p,d) 分離性から得た p 分離性を使う。原典とは異なる直接比較の経路。

## 規約

p の正則性や台環の有界 p ねじれは仮定しない。基底射の存在自体はまだ主張しない。

## 使われ方

一般有界 prism への Witt 環からの持上げで、台環の古典的 p 完備性を供給する。
-/

@[expose] public noncomputable section BoundedPrismPrimeComplete

namespace SerrePositivity.BhattScholze

/-- 概要：導来主元完備かつ主元進分離な環は古典的に主元進完備。
方針：差分作用の全射性から前完備性を得て、分離性と合わせる。
規約：主元の正則性は要求しない。
使われ方：BS 著者版 Lemma 4.8（著者版 pp.38–39）の一般有界標的への持上げの準備。 -/
theorem isAdicComplete_of_isModuleComplete_of_isHausdorff
    (R : Type u) [CommRing R] (a : R)
    (h : _root_.SerrePositivity.DerivedCompletion.IsModuleComplete R a (ModuleCat.of R R))
    [IsHausdorff (Ideal.span {a}) R] : IsAdicComplete (Ideal.span {a}) R := by
  have hb := (_root_.SerrePositivity.DerivedCompletion.isModuleComplete_iff_recurrence_bijective
    R a (ModuleCat.of R R)).mp h
  let := _root_.SerrePositivity.isPrecomplete_of_adicRecurrenceMap_surjective a hb.2
  exact ⟨⟩

/-- 概要：有界 prism の台環は古典的に p 完備である。
方針：導来 p 完備性と (p,d) 分離性からの p 分離性を一般比較へ渡す。
規約：標的の完全性・p 正則性・台環の有界 p ねじれは要求しない。
使われ方：完全 prism から有界標的への入力射の構成。 -/
theorem boundedPrism_isAdicComplete_prime
    {B : Type u} [CommRing B] {p : ℕ} [Fact p.Prime] (Q : _root_.SerrePositivity.BhattScholze.OrientedPrism p B)
    (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
      (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0) :
    IsAdicComplete (Ideal.span {(p : B)}) B := by
  let := _root_.SerrePositivity.BhattScholze.boundedPrism_isHausdorff_prime Q hB
  exact _root_.SerrePositivity.BhattScholze.isAdicComplete_of_isModuleComplete_of_isHausdorff B (p : B) Q.complete_p

end SerrePositivity.BhattScholze

end BoundedPrismPrimeComplete

/-! ## 完全 prism の共通二元イデアルに沿う古典的完備性

## 概要

完全 prism の台環は (p,d) に沿って古典的完備である。
BS 著者版 Remark 7.15（著者版 p.62）の剰余根列の一意持上げに用いる完備性。

## 方針

生成元の全冪商の p 完備性を、二つのイデアルの和に沿う完備性の一般定理へ渡す。
原典とは異なる、有界ねじれによる古典的完備性と共通完備商を使う経路。

## 規約

prism 商の p 正則性や非零性は要求しない。

## 使われ方

Perfection の完備商同型に必要な、台環の共通 (p,d) 完備性を供給する。
-/

@[expose] public noncomputable section PerfectPrismPairAdicComplete

namespace SerrePositivity.BhattScholze
variable {B : Type u} [CommRing B] {p : ℕ} [Fact p.Prime]
variable (Q : _root_.SerrePositivity.BhattScholze.OrientedPrism p B) (hQ : Q.deltaStructure.IsPerfect)

include hQ in
/-- 概要：完全 prism の生成元の全冪商は元の p イデアルに沿って完備。
方針：distinguished 冪商の p 完備性を、元の係数環による作用へ戻す。
規約：零冪商・零環も含み、商の p 正則性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の共通二元イデアルの完備性への入力。 -/
theorem perfectPrism_generator_power_quotient_prime_complete (n : ℕ) :
    IsAdicComplete (Ideal.span {(p : B)}) (B ⧸ (Ideal.span {Q.generator}) ^ n) := by
  let := Q.isAdicComplete_p_of_perfect hQ
  rw [Ideal.span_singleton_pow]
  apply (IsAdicComplete.map_algebraMap_iff
    (I := Ideal.span {(p : B)}) (S := B ⧸ Ideal.span {Q.generator ^ n})
    (M := B ⧸ Ideal.span {Q.generator ^ n})).mp
  simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using
    hQ.distinguished_power_quotient_isAdicComplete (Q.isDistinguished_generator) n

include hQ in
/-- 概要：完全 prism の台環は (p,d) に沿って古典的完備（BS 著者版 Lemma 3.8 (2) の完備性を与える向き付きの場合）。
方針：d 完備性と全 d 冪商の p 完備性から和イデアルの完備性を構成する。
規約：p,d が正則列であることは要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の台環と prism 商の共通完備商。 -/
theorem perfectPrism_pair_isAdicComplete :
    IsAdicComplete (Ideal.span {(p : B), Q.generator}) B := by
  let := Q.isAdicComplete_generator
  let : ∀ n : ℕ, IsAdicComplete (Ideal.span {(p : B)})
      (B ⧸ (Ideal.span {Q.generator}) ^ n) :=
    _root_.SerrePositivity.BhattScholze.perfectPrism_generator_power_quotient_prime_complete Q hQ
  have he : Ideal.span {Q.generator} ⊔ Ideal.span {(p : B)} =
      Ideal.span {(p : B), Q.generator} := by
    rw [← Ideal.span_union, Set.singleton_union]
    exact Ideal.span_pair_comm
  rw [← he]
  exact _root_.SerrePositivity.isAdicComplete_sup_of_complete_quotients (Ideal.span {Q.generator}) (Ideal.span {(p : B)})

end SerrePositivity.BhattScholze

end PerfectPrismPairAdicComplete

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Lemma 3.7" (partial := special) "(1) と (2)（完全平坦な複体の離散性、通常の導来圏で、BS-W15 K4）、(3)（完全平坦な δ 代数から有界 prism、exists_boundedPrism_of_completelyFlat_deltaAlgebra）は本体。(4) は不要（D19）。向き付きの基底 ／ 11-11 更新（2） ／ 11-12 夜更新（ノート本文の更新時）"] _root_.SerrePositivity.BhattScholze.boundedPrism_pair_isAdicComplete
attribute [cite BS19 "Lemma 3.8" (partial := special) "向き付きなので (1) の単項性は定義に含まれる。(2) は A/d の p 冪ねじれが p で消えること・完備性として証明済み。Thm 3.10・A4 Lemma 8.4 で使う ／ DOC1 照合（11-07、Codex が型で確認）：項目そのものではないので宣言の列から外したもの：isAdicComplete_p_of_perfect（完全 prism の古典 (p,I) 進完備性と結論が異なる。）；distinguished_quotient_isAdicComplete（Lemma 3.8 (2) の完備性は A 上。商の完備性は Theorem 3.10 の証明に現れる別の帰結。） ／ DOC1 照合：ok 2 件 ／ 11-12 夜更新（§3 の見直し）"] _root_.SerrePositivity.BhattScholze.perfectPrism_pair_isAdicComplete
