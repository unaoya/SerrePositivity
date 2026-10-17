module

public import SerrePositivity.BhattScholze.Andre.PerfectPrismVarpi

/-!
# André E1・E2：ϖ 商から p 商への具体的 Frobenius 同型

## 概要

完全 prism (A,(d)) の商 R で、選択した ϖ に対し R/ϖ と R/p は Frobenius で環同型。
BS Rem 7.15（著者版 p.62）の Frobenius 引戻しで二つの係数環を追跡する。

## 方針

A の Frobenius 同型は (d,φ⁻¹(d)) を (φ(d),d)=(p,d) へ送る。
二重主イデアル商の同型と合成して代表元上の作用を計算する。

## 規約

順方向は R/ϖ から R/p。prism 商の p 正則性は要求しない。

## 使われ方

raw 除算包の二重剰余と通常 pd 包の係数作用を比較するための具体的な係数同型。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
local notation "D" => W.deltaStructure
local notation "x" => perfectPrismVarpiLift W hW
local notation "R" => A ⧸ W.ideal
local notation "Rv" => R ⧸ Ideal.span {perfectPrismVarpi W hW}
local notation "Rp" => R ⧸ Ideal.span {(p : R)}

/-- 概要：係数 Frobenius は (d,x) を (p,d) へ送る。
方針：φ(x)=d と distinguished 元 d の二元イデアルの計算を使う。
規約：等式は A 内のイデアルの像として述べる。
使われ方：BS Rem 7.15（著者版 p.62）の剰余係数環の比較。 -/
theorem perfectPrismVarpiFrobenius_pairIdeal :
    (Ideal.span {W.generator, x}).map ((D).frobeniusEquiv hW).toRingHom =
      Ideal.span {(p : A), W.generator} := by
  rw [Ideal.map_span, Set.image_pair]
  change Ideal.span {(D).frobeniusLift W.generator, (D).frobeniusLift x} = _
  rw [perfectPrismVarpiLift_frobenius]
  exact distinguished_frobenius_pair_span _ _ (W.isDistinguished_of_perfect hW)

/-- 概要：R/ϖ と R/p の具体的な Frobenius 環同型。
方針：二元商上の係数 Frobenius を二重主イデアル商の同型と合成する。
規約：指定生成元とその逆 Frobenius 像から選んだ ϖ を用いる。
使われ方：BS Rem 7.15（著者版 p.62）の Frobenius 係数作用を明示する。 -/
def perfectPrismVarpiFrobeniusQuotientEquiv : Rv ≃+* Rp :=
  (((principalDoubleQuotEquiv W.generator x).trans
    (Ideal.quotientEquiv _ (Ideal.span {W.generator, (p : A)}) ((D).frobeniusEquiv hW)
      ((Ideal.span_pair_comm).trans (perfectPrismVarpiFrobenius_pairIdeal W hW).symm))).trans
    (principalDoubleQuotEquiv W.generator (p : A)).symm).trans
      (Ideal.quotEquivOfEq (show Ideal.span {Ideal.Quotient.mk W.ideal (p : A)} =
        Ideal.span {(p : R)} by rw [map_natCast]))

/-- 概要：係数商同型は A の代表元に Frobenius を適用する。
方針：二重商と商同型の代表元公式を使う。
規約：順方向の係数作用を全ての b:A で指定する。
使われ方：BS Rem 7.15（著者版 p.62）の入力多項式の係数比較。 -/
theorem perfectPrismVarpiFrobeniusQuotientEquiv_mk (b : A) :
    perfectPrismVarpiFrobeniusQuotientEquiv W hW
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk W.ideal b)) =
        Ideal.Quotient.mk _ (Ideal.Quotient.mk W.ideal ((D).frobeniusLift b)) := by
  have hs : principalDoubleQuotEquiv W.generator x
      (Ideal.Quotient.mk (Ideal.span {perfectPrismVarpi W hW})
        (Ideal.Quotient.mk W.ideal b)) = Ideal.Quotient.mk _ b := by
    unfold perfectPrismVarpi
    exact principalDoubleQuotEquiv_mk W.generator x b
  have ht := principalDoubleQuotEquiv_mk W.generator (p : A) ((D).frobeniusLift b)
  have ht' := (principalDoubleQuotEquiv W.generator (p : A)).symm_apply_apply
    (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ ((D).frobeniusLift b)))
  rw [ht] at ht'
  simp only [perfectPrismVarpiFrobeniusQuotientEquiv, RingEquiv.trans_apply]
  erw [hs, Ideal.quotientEquiv_mk]
  change Ideal.quotEquivOfEq _
    ((principalDoubleQuotEquiv W.generator (p : A)).symm
      (Ideal.Quotient.mk _ ((D).frobeniusLift b))) = _
  rw [ht', Ideal.quotEquivOfEq_mk]
  rfl

/-- 概要：この係数同型は R の元の p 乗を R/p で取る写像に一致する。
方針：φ(b)=b^p+pδ(b) を二重商へ移し、p の項を消す。
規約：A の代表元で述べ、係数環への非零性を仮定しない。
使われ方：BS Rem 7.15（著者版 p.62）の係数 Frobenius と通常 p 乗の照合。 -/
theorem perfectPrismVarpiFrobeniusQuotientEquiv_mk_pow (b : A) :
    perfectPrismVarpiFrobeniusQuotientEquiv W hW
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk W.ideal b)) =
        Ideal.Quotient.mk (Ideal.span {(p : R)}) ((Ideal.Quotient.mk W.ideal b) ^ p) := by
  rw [perfectPrismVarpiFrobeniusQuotientEquiv_mk, (D).frobeniusLift_apply,
    map_add, map_pow, map_mul, map_natCast, map_add, map_mul]
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self (p : R)),
    zero_mul, add_zero]

end SerrePositivity.BhattScholze.Andre
