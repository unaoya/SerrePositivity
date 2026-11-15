module

public import Mathlib.RingTheory.Teichmuller
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.CharP.Algebra
public import SerrePositivity.BhattScholze.Prism.Bounded.Completeness
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Torsion

/-!
# 有界 prism とその商の tilt

## 概要
共通の標数 p 商に沿って完備な環の互換 p 冪根列の一意な持ち上げ、完全・有界 prism の商の互換根列の持ち上げ、
有界 prism の台環と商の tilt の同型。

## 方針
互換根列を共通商で持ち上げ、完備性で収束させる。

## 規約
向き付き。

## 使われ方
BS 著者版 Lemma 4.8 の証明。旧 Andre/Remark715 から移した。
-/

universe u v

/-! ## 共通の標数 p 完備商を介する互換根列の一意持上げ

## 概要

J≤I に対し、環 B と B/J が共通の標数 p 商 B/I に沿って完備なら、
B/J 内の互換 p 冪根列は B 内へ一意に持ち上がる。
BS 著者版 Remark 7.15（著者版 p.62）の prismatic 入力射の持上げの準備。

## 方針

互換根列を表す乗法モノイド Perfection を、二つの完備商の Teichmüller 同型で比較する。
原典とは異なる共通完備商とモノイド同型による具体的な経路。

## 規約

分母・係数元の正則性や δ 構造は不要。二つの古典的完備性と標数を明示する。

## 使われ方

試験 prism の剰余上の根列を、元の台環内の実根列へ持ち上げる。
-/

@[expose] public noncomputable section CommonAdicCompatibleRoots

namespace SerrePositivity.BhattScholze

/-- 概要：乗法モノイド同型は互換根列のモノイド同型を誘導する。
方針：全座標に同型と逆同型を作用させる。
規約：ここでは素数性や環構造を要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の二つの共通剰余の比較。 -/
def perfectionCongrMulEquiv (p : ℕ) {M : Type u} {N : Type v}
    [CommMonoid M] [CommMonoid N] (e : M ≃* N) : Perfection M p ≃* Perfection N p :=
  { Perfection.mapMonoidHom p e.toMonoidHom with
    invFun := Perfection.mapMonoidHom p e.symm.toMonoidHom
    left_inv := by
      intro x
      apply Perfection.extMonoid
      intro n
      exact e.symm_apply_apply _
    right_inv := by
      intro x
      apply Perfection.extMonoid
      intro n
      exact e.apply_symm_apply _ }

variable {B : Type u} [CommRing B] (p : ℕ) [Fact p.Prime]
variable (I J : Ideal B) (hJI : J ≤ I)
variable [CharP (B ⧸ I) p] [IsAdicComplete I B]
variable [IsAdicComplete (I.map (Ideal.Quotient.mk J)) (B ⧸ J)]

/-- 概要：共通の標数 p 完備商を持つ商射は互換根列のモノイド同型を誘導する。
方針：二つの Teichmüller 同型と第三同型定理を合成し、順射を元の商射と照合する。
規約：順射の全座標は元の B→B/J の商射と一致する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の剰余根列の一意持上げ。 -/
def perfectionQuotientEquivOfCommonAdic : Perfection B p ≃* Perfection (B ⧸ J) p := by
  let K := I.map (Ideal.Quotient.mk J)
  let e : (B ⧸ J) ⧸ K ≃+* B ⧸ I := DoubleQuot.quotQuotEquivQuotOfLE hJI
  let : CharP ((B ⧸ J) ⧸ K) p :=
    charP_of_injective_ringHom (f := e.symm.toRingHom) e.symm.injective p
  let eB := Perfection.quotientMulEquiv p I
  let eC := Perfection.quotientMulEquiv p K
  let eD := _root_.SerrePositivity.BhattScholze.perfectionCongrMulEquiv p e.toMulEquiv
  let E := eB.trans (eD.symm.trans eC.symm)
  let q := Perfection.mapMonoidHom p (Ideal.Quotient.mk J : B →* B ⧸ J)
  have he (x : Perfection B p) : E x = q x := by
    apply eC.injective
    change eC (eC.symm (eD.symm (eB x))) = eC (q x)
    rw [eC.apply_symm_apply]
    apply eD.injective
    rw [eD.apply_symm_apply]
    apply Perfection.extMonoid
    intro n
    rfl
  exact { q with
    invFun := E.symm
    left_inv := fun x => by
      change E.symm (q x) = x
      rw [← he]
      exact E.symm_apply_apply x
    right_inv := fun x => by
      change q (E.symm x) = x
      rw [← he]
      exact E.apply_symm_apply x }

/-- 概要：互換根列の比較同型の順射は各座標で元の商写像。
方針：順射を商写像の Perfection として定義した計算規則を使う。
規約：全ての段 n と全ての根列を含む。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の持上げの剰余値の検証。 -/
theorem perfectionQuotientEquivOfCommonAdic_coeff (x : Perfection B p) (n : ℕ) :
    Perfection.coeffMonoidHom (B ⧸ J) p n
      (_root_.SerrePositivity.BhattScholze.perfectionQuotientEquivOfCommonAdic p I J hJI x) =
        Ideal.Quotient.mk J (Perfection.coeffMonoidHom B p n x) := rfl

include I hJI in
/-- 概要：共通の標数 p 完備商があると、剰余内の互換根列は台環へ一意に持ち上がる。
方針：根列のモノイド同型の逆を用い、座標上の商公式と単射性を使う。
規約：元ごとの根の選択ではなく、列全体の一意持上げを述べる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の絶対入力射へ向けた根列の持上げ。 -/
theorem existsUnique_compatiblePowerRootsLift_of_common_adic
    (ρ : ℕ → B ⧸ J) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) :
    ∃! σ : ℕ → B,
      (∀ n, σ (n + 1) ^ p = σ n) ∧ ∀ n, Ideal.Quotient.mk J (σ n) = ρ n := by
  let e := _root_.SerrePositivity.BhattScholze.perfectionQuotientEquivOfCommonAdic p I J hJI
  let y : Perfection (B ⧸ J) p := ⟨ρ, hρ⟩
  let x := e.symm y
  refine ⟨fun n => Perfection.coeffMonoidHom B p n x, ⟨?_, ?_⟩, ?_⟩
  · intro n
    exact Perfection.coeffMonoidHom_pow_p' x n
  · intro n
    exact congrArg (Perfection.coeffMonoidHom (B ⧸ J) p n) (e.apply_symm_apply y)
  · intro σ hσ
    let z : Perfection B p := ⟨σ, hσ.1⟩
    have hz : e z = y := by
      apply Perfection.extMonoid
      intro n
      exact hσ.2 n
    have hzx : z = x := e.injective (hz.trans (e.apply_symm_apply y).symm)
    funext n
    exact congrArg (Perfection.coeffMonoidHom B p n) hzx

omit [CharP (B ⧸ I) p] in
include hJI in
/-- 概要：p を含む共通完備商があれば、零環も含めて互換根列は一意に持ち上がる。
方針：非零の共通商に標数 p を供給し、零商の場合は完備性から台環も零と示す。
規約：標数インスタンスや非零性を追加仮定に残さない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の任意の試験環に使える根列の持上げ。 -/
theorem existsUnique_compatiblePowerRootsLift_of_adic_ideals
    (hpI : (p : B) ∈ I) (ρ : ℕ → B ⧸ J) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) :
    ∃! σ : ℕ → B,
      (∀ n, σ (n + 1) ^ p = σ n) ∧ ∀ n, Ideal.Quotient.mk J (σ n) = ρ n := by
  rcases subsingleton_or_nontrivial (B ⧸ I) with hs | hn
  · have hItop : I = ⊤ := Ideal.Quotient.subsingleton_iff.mp hs
    have h10 : (1 : B) = 0 := by
      apply IsHausdorff.haus' (I := I)
      intro n
      apply SModEq.sub_mem.mpr
      simp [hItop, Ideal.top_pow]
    let : Subsingleton B := subsingleton_of_zero_eq_one h10.symm
    refine ⟨fun _ => 0, ⟨?_, ?_⟩, ?_⟩
    · intro n
      exact zero_pow (Fact.out : p.Prime).ne_zero
    · intro n
      exact Subsingleton.elim _ _
    · intro σ _
      exact Subsingleton.elim _ _
  · let := hn
    let : CharP (B ⧸ I) p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr
      (by simpa only [map_natCast] using Ideal.Quotient.eq_zero_iff_mem.mpr hpI)
    exact _root_.SerrePositivity.BhattScholze.existsUnique_compatiblePowerRootsLift_of_common_adic p I J hJI ρ hρ

end SerrePositivity.BhattScholze

end CommonAdicCompatibleRoots

/-! ## 完全試験 prism の剰余互換根列の一意持上げ

## 概要

完全 prism の商にある互換 p 冪根列は、台環内の互換根列へ一意に持ち上がる。
BS 著者版 Remark 7.15（著者版 p.62）の絶対 prismatic 入力射の完全試験環での持上げ。

## 方針

台環の (p,d) 完備性と商の p 完備性を、共通完備商による Perfection の同型へ供給する。
原典とは異なる Teichmüller モノイド比較による経路。

## 規約

試験 prism の完全性を明示する。商の p 正則性・非零性は仮定しない。
一般の試験 prism に対する同じ完備性の供給は別工程。

## 使われ方

剰余根列を入力として、完全試験 prism への実完備化の普遍射を作る。
-/

@[expose] public noncomputable section PerfectPrismCompatibleRootsLift

namespace SerrePositivity.BhattScholze
variable {B : Type u} [CommRing B] {p : ℕ} [Fact p.Prime]
variable (Q : _root_.SerrePositivity.BhattScholze.OrientedPrism p B)

/-- 概要：共通二元イデアルの prism 商での像は p 主イデアル。
方針：商で生成元 d が零になることを二元生成イデアルの像へ代入する。
規約：この計算自体に完全性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の二つの古典的完備性の比較。 -/
theorem prism_pair_map_ideal_eq_prime :
    (Ideal.span {(p : B), Q.generator}).map (Ideal.Quotient.mk Q.ideal) =
      Ideal.span {(p : B ⧸ Q.ideal)} := by
  rw [Ideal.map_span, Set.image_pair, map_natCast]
  have hd : Ideal.Quotient.mk Q.ideal Q.generator = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self Q.generator)
  rw [hd, Ideal.span_pair_zero]

/-- 概要：完全 prism 商の互換根列は台環内へ一意に持ち上がる。
方針：(p,d) 完備性と商の p 完備性を共通完備商の根列持上げへ適用する。
規約：零環を含み、商の p 正則性を仮定しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完全試験 prism 内への根列の持上げ。 -/
theorem existsUnique_perfectPrismCompatibleRootsLift
    (hQ : Q.deltaStructure.IsPerfect) (ρ : ℕ → B ⧸ Q.ideal)
    (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) :
    ∃! σ : ℕ → B,
      (∀ n, σ (n + 1) ^ p = σ n) ∧ ∀ n, Ideal.Quotient.mk Q.ideal (σ n) = ρ n := by
  let I := Ideal.span {(p : B), Q.generator}
  let := Q.isAdicComplete_p_of_perfect hQ
  let : IsAdicComplete I B := _root_.SerrePositivity.BhattScholze.perfectPrism_pair_isAdicComplete Q hQ
  let : IsAdicComplete (Ideal.span {(p : B ⧸ Q.ideal)}) (B ⧸ Q.ideal) :=
    hQ.distinguished_quotient_isAdicComplete (Q.isDistinguished_generator)
  let : IsAdicComplete (I.map (Ideal.Quotient.mk Q.ideal)) (B ⧸ Q.ideal) := by
    rw [_root_.SerrePositivity.BhattScholze.prism_pair_map_ideal_eq_prime]
    infer_instance
  have hJI : Q.ideal ≤ I := by
    apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact Ideal.subset_span (by simp)
  exact _root_.SerrePositivity.BhattScholze.existsUnique_compatiblePowerRootsLift_of_adic_ideals p I Q.ideal hJI
    (Ideal.subset_span (by simp)) ρ hρ

end SerrePositivity.BhattScholze

end PerfectPrismCompatibleRootsLift

/-! ## 一般有界試験 prism の剰余互換根列の一意持上げ

## 概要

有界 prism の商内の互換 p 冪根列は、台環内の互換根列へ一意に持ち上がる。
BS 著者版 Remark 7.15（著者版 p.62）の prismatic 入力射の持上げに使う。

## 方針

生成元の全冪商の有界ねじれから (p,d) 完備性を供給し、共通完備商の Perfection 同型を使う。
原典とは異なる有界指数の帰納計算と Teichmüller モノイド比較による経路。

## 規約

試験 prism の完全性・p 正則性・商の非零性は不要。有界 p 冪ねじれのみを明示する。

## 使われ方

一般有界試験 prism の剰余根データから実入力 δ 射を作る。
-/

@[expose] public noncomputable section BoundedPrismCompatibleRootsLift

namespace SerrePositivity.BhattScholze
variable {B : Type u} [CommRing B] {p : ℕ} [Fact p.Prime]
variable (Q : _root_.SerrePositivity.BhattScholze.OrientedPrism p B)

/-- 概要：有界 prism 商の互換根列は台環内へ一意に持ち上がる。
方針：台環の (p,d) 完備性と商の p 完備性を共通完備商の一般結果へ渡す。
規約：完全性や p 正則性を要求せず、零環も含む。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の一般有界試験 prism への根列の持上げ。 -/
theorem existsUnique_boundedPrismCompatibleRootsLift
    (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
      (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0)
    (ρ : ℕ → B ⧸ Q.ideal) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) :
    ∃! σ : ℕ → B,
      (∀ n, σ (n + 1) ^ p = σ n) ∧ ∀ n, Ideal.Quotient.mk Q.ideal (σ n) = ρ n := by
  let I := Ideal.span {(p : B), Q.generator}
  let : IsAdicComplete I B := _root_.SerrePositivity.BhattScholze.boundedPrism_pair_isAdicComplete Q hB
  let : IsAdicComplete (Ideal.span {(p : B ⧸ Q.ideal)}) (B ⧸ Q.ideal) :=
    _root_.SerrePositivity.BhattScholze.boundedPrism_quotient_isAdicComplete_prime Q hB
  let : IsAdicComplete (I.map (Ideal.Quotient.mk Q.ideal)) (B ⧸ Q.ideal) := by
    rw [_root_.SerrePositivity.BhattScholze.prism_pair_map_ideal_eq_prime]
    infer_instance
  have hJI : Q.ideal ≤ I := by
    apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact Ideal.subset_span (by simp)
  exact _root_.SerrePositivity.BhattScholze.existsUnique_compatiblePowerRootsLift_of_adic_ideals p I Q.ideal hJI
    (Ideal.subset_span (by simp)) ρ hρ

end SerrePositivity.BhattScholze

end BoundedPrismCompatibleRootsLift

/-! ## André 有界 prism の台環と商の tilt 比較

## 概要

有界 prism の台環から prism 商への射は tilt の環同型を誘導する。
BS 著者版 Lemma 4.8（著者版 pp.38–39）の基底環射の構成への準備。

## 方針

二つの p 完備環の tilt を実互換根列と乗法的に比較する。
既知の prism 商からの根列の一意持上げにより標準 tilt 環射の全単射性を示す。
原典の変形理論とは異なる Teichmüller 比較の経路。

## 規約

標的 prism の完全性・p 正則性は要求しない。台環と prism 商で p が非可逆である場合を扱う。
台環での非可逆性は商での非可逆性から従うが、型クラス用に明示する。

## 使われ方

商の tilt へ写された完全係数を台環の tilt へ戻し、Fontaine 写像による環射構成に用いる。
-/

@[expose] public noncomputable section BoundedPrismTiltQuotient

namespace SerrePositivity.BhattScholze
variable {B : Type u} [CommRing B] {p : ℕ} [Fact p.Prime]
variable (Q : _root_.SerrePositivity.BhattScholze.OrientedPrism p B)
variable [Fact (¬ IsUnit (p : B))]
variable [Fact (¬ IsUnit (p : B ⧸ Q.ideal))]

variable (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
  (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0)

include hB in
/-- 概要：有界 prism の商射が誘導する標準 tilt 環射は全単射。
方針：二つの p 完備性から実根列と比較し、既存の根列の一意持上げを使う。
規約：台環と商での p 非可逆性を標数インスタンス用に明示する。
使われ方：BS 著者版 Lemma 4.8（著者版 pp.38–39）の基底環射を tilt から構成する。 -/
theorem boundedPrism_preTiltQuotient_bijective :
    Function.Bijective (Perfection.map p (_root_.SerrePositivity.modPMap p (Ideal.Quotient.mk Q.ideal))) := by
  let q := Ideal.Quotient.mk Q.ideal
  let := _root_.SerrePositivity.BhattScholze.boundedPrism_isAdicComplete_prime Q hB
  let := _root_.SerrePositivity.BhattScholze.boundedPrism_quotient_isAdicComplete_prime Q hB
  let eB := Perfection.quotientMulEquiv p (Ideal.span {(p : B)})
  let eC := Perfection.quotientMulEquiv p (Ideal.span {(p : B ⧸ Q.ideal)})
  let M := Perfection.mapMonoidHom p q.toMonoidHom
  have hM : Function.Bijective M := by
    have hex (y : Perfection (B ⧸ Q.ideal) p) : ∃! x : Perfection B p, M x = y := by
      obtain ⟨σ, hσ, hu⟩ := _root_.SerrePositivity.BhattScholze.existsUnique_boundedPrismCompatibleRootsLift Q hB
        (fun n => Perfection.coeffMonoidHom (B ⧸ Q.ideal) p n y)
        (fun n => Perfection.coeffMonoidHom_pow_p' y n)
      let x : Perfection B p := ⟨σ, hσ.1⟩
      refine ⟨x, ?_, ?_⟩
      · exact Perfection.extMonoid hσ.2
      · intro z hz
        have hc : (fun n => Perfection.coeffMonoidHom B p n z) = σ := by
          apply hu
          constructor
          · exact fun n => Perfection.coeffMonoidHom_pow_p' z n
          · intro n
            exact congrArg (Perfection.coeffMonoidHom (B ⧸ Q.ideal) p n) hz
        exact Perfection.extMonoid (congrFun hc)
    constructor
    · intro x y hxy
      obtain ⟨z, hz, hu⟩ := hex (M x)
      exact (hu x rfl).trans (hu y hxy.symm).symm
    · intro y
      obtain ⟨x, hx, _⟩ := hex y
      exact ⟨x, hx⟩
  have hcomm (x : Perfection B p) :
      Perfection.map p (_root_.SerrePositivity.modPMap p q) (eB x) = eC (M x) := by
    apply Perfection.ext
    intro n
    rfl
  constructor
  · intro x y hxy
    have he : M (eB.symm x) = M (eB.symm y) := by
      apply eC.injective
      rw [← hcomm, ← hcomm, eB.apply_symm_apply, eB.apply_symm_apply, hxy]
    have h := congrArg eB (hM.injective he)
    simpa only [eB.apply_symm_apply] using h
  · intro y
    obtain ⟨x, hx⟩ := hM.surjective (eC.symm y)
    refine ⟨eB x, ?_⟩
    rw [hcomm, hx, eC.apply_symm_apply]

/-- 概要：有界 prism の台環と prism 商の tilt は標準商射により環同型。
方針：標準 tilt 環射の全単射性から環同型を作る。
規約：完全性や p 正則性を追加せず、有界性と台環・商での p 非可逆性を明示する。
使われ方：BS 著者版 Lemma 4.8（著者版 pp.38–39）の完全係数の台環への持上げ。 -/
def boundedPrism_preTiltQuotientEquiv : PreTilt B p ≃+* PreTilt (B ⧸ Q.ideal) p := by
  exact RingEquiv.ofBijective
    (Perfection.map p (_root_.SerrePositivity.modPMap p (Ideal.Quotient.mk Q.ideal)))
    (_root_.SerrePositivity.BhattScholze.boundedPrism_preTiltQuotient_bijective Q hB)

/-- 概要：tilt 比較同型の各座標は標準 mod p 商射で与えられる。
方針：全単射から作った環同型の順射の定義を展開する。
規約：全ての根段 n で同じ標準商射を使う。
使われ方：BS 著者版 Lemma 4.8（著者版 pp.38–39）の Fontaine 写像との可換図式。 -/
theorem boundedPrism_preTiltQuotientEquiv_coeff (x : PreTilt B p) (n : ℕ) :
    PreTilt.coeff n (_root_.SerrePositivity.BhattScholze.boundedPrism_preTiltQuotientEquiv Q hB x) =
      _root_.SerrePositivity.modPMap p (Ideal.Quotient.mk Q.ideal) (PreTilt.coeff n x) := rfl

end SerrePositivity.BhattScholze

end BoundedPrismTiltQuotient
