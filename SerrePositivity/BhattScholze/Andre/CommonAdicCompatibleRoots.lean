module

public import Mathlib.RingTheory.Teichmuller
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.CharP.Algebra

/-!
# André E1・E2：共通の標数 p 完備商を介する互換根列の一意持上げ

## 概要

J≤I に対し、環 B と B/J が共通の標数 p 商 B/I に沿って完備なら、
B/J 内の互換 p 冪根列は B 内へ一意に持ち上がる。
BS Rem 7.15（著者版 p.62）の prismatic 入力射の持上げの準備。

## 方針

互換根列を表す乗法モノイド Perfection を、二つの完備商の Teichmüller 同型で比較する。
原典とは異なる共通完備商とモノイド同型による具体的な経路。

## 規約

分母・係数元の正則性や δ 構造は不要。二つの古典的完備性と標数を明示する。

## 使われ方

試験 prism の剰余上の根列を、元の台環内の実根列へ持ち上げる。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze.Andre

/-- 概要：乗法モノイド同型は互換根列のモノイド同型を誘導する。
方針：全座標に同型と逆同型を作用させる。
規約：ここでは素数性や環構造を要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の二つの共通剰余の比較。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の剰余根列の一意持上げ。 -/
def perfectionQuotientEquivOfCommonAdic : Perfection B p ≃* Perfection (B ⧸ J) p := by
  let K := I.map (Ideal.Quotient.mk J)
  let e : (B ⧸ J) ⧸ K ≃+* B ⧸ I := DoubleQuot.quotQuotEquivQuotOfLE hJI
  let : CharP ((B ⧸ J) ⧸ K) p :=
    charP_of_injective_ringHom (f := e.symm.toRingHom) e.symm.injective p
  let eB := Perfection.quotientMulEquiv p I
  let eC := Perfection.quotientMulEquiv p K
  let eD := perfectionCongrMulEquiv p e.toMulEquiv
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
使われ方：BS Rem 7.15（著者版 p.62）の持上げの剰余値の検証。 -/
theorem perfectionQuotientEquivOfCommonAdic_coeff (x : Perfection B p) (n : ℕ) :
    Perfection.coeffMonoidHom (B ⧸ J) p n
      (perfectionQuotientEquivOfCommonAdic p I J hJI x) =
        Ideal.Quotient.mk J (Perfection.coeffMonoidHom B p n x) := rfl

include I hJI in
/-- 概要：共通の標数 p 完備商があると、剰余内の互換根列は台環へ一意に持ち上がる。
方針：根列のモノイド同型の逆を用い、座標上の商公式と単射性を使う。
規約：元ごとの根の選択ではなく、列全体の一意持上げを述べる。
使われ方：BS Rem 7.15（著者版 p.62）の絶対入力射へ向けた根列の持上げ。 -/
theorem existsUnique_compatiblePowerRootsLift_of_common_adic
    (ρ : ℕ → B ⧸ J) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) :
    ∃! σ : ℕ → B,
      (∀ n, σ (n + 1) ^ p = σ n) ∧ ∀ n, Ideal.Quotient.mk J (σ n) = ρ n := by
  let e := perfectionQuotientEquivOfCommonAdic p I J hJI
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
使われ方：BS Rem 7.15（著者版 p.62）の任意の試験環に使える根列の持上げ。 -/
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
    exact existsUnique_compatiblePowerRootsLift_of_common_adic p I J hJI ρ hρ

end SerrePositivity.BhattScholze.Andre
