module

public import SerrePositivity.BhattScholze.Prism.Basic.PerfectOrientedPrism
public import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDelta
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# André E1・E2：完全 prism の生成元から選ぶ ϖ

## 概要

完全 prism (A,(d)) で x=φ⁻¹(d) と置く。R=A/(d) 内の像 ϖ は (ϖ^p)=(p) を満たす。
さらに A 内で (d,x)=(p,x) となる。
BS Rem 7.15（著者版 p.62）の係数商の比較に必要な具体的な選択である。

## 方針

逆 Frobenius が δ 射なので δ(x) は単元。d=x^p+pδ(x) を商へ移す。

## 規約

prism の指定生成元を使用する。R の p 正則性はここでは仮定しない。

## 使われ方

原典の R/ϖ と A/(p,x) の比較への入力。prismatic envelope の同定は主張しない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 概要：prism 生成元の Frobenius 逆像を選ぶ。
方針：完全 δ 環の Frobenius 同型の逆を使う。
規約：指定生成元を使用する。
使われ方：BS Rem 7.15（著者版 p.62）の ϖ の持上げ。 -/
def perfectPrismVarpiLift (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) : A :=
  (W.deltaStructure.frobeniusEquiv hW).symm W.generator

/-- 概要：選んだ持上げの Frobenius は prism 生成元。
方針：環同型の逆合成を使う。
規約：等式は A 内で述べる。
使われ方：BS Rem 7.15（著者版 p.62）の係数計算。 -/
theorem perfectPrismVarpiLift_frobenius (W : OrientedPrism p A)
    (hW : W.deltaStructure.IsPerfect) :
    W.deltaStructure.frobeniusLift (perfectPrismVarpiLift W hW) = W.generator :=
  (W.deltaStructure.frobeniusEquiv hW).apply_symm_apply W.generator

/-- 概要：ϖ の持上げは distinguished 元。
方針：生成元の distinguished 性を逆 Frobenius の δ 射で移す。
規約：単元性は A 内で述べる。
使われ方：BS Rem 7.15（著者版 p.62）の p と ϖ^p の比較。 -/
theorem perfectPrismVarpiLift_delta_isUnit (W : OrientedPrism p A)
    (hW : W.deltaStructure.IsPerfect) :
    IsUnit (W.deltaStructure.delta (perfectPrismVarpiLift W hW)) := by
  have h := (W.isDistinguished_of_perfect hW).map
    (W.deltaStructure.frobeniusEquiv hW).symm.toRingHom
  change IsUnit ((W.deltaStructure.frobeniusEquiv hW).symm.toRingHom
    (W.deltaStructure.delta W.generator)) at h
  rw [W.deltaStructure.frobeniusEquiv_symm_isDeltaHom hW W.generator] at h
  exact h

/-- 概要：ϖ は Frobenius 逆像の prism 商への像。
方針：指定 prism イデアルの標準商射を使う。
規約：台環は A/(d)。
使われ方：BS Rem 7.15（著者版 p.62）の係数元。 -/
def perfectPrismVarpi (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) :
    A ⧸ W.ideal := Ideal.Quotient.mk W.ideal (perfectPrismVarpiLift W hW)

/-- 概要：選んだ ϖ の p 乗は p と明示的な単元の積。
方針：φ(x)=x^p+pδ(x)=d を prism 商へ移す。
規約：単元因子は −δ(x) の商像。
使われ方：BS Rem 7.15（著者版 p.62）の (ϖ^p)=(p)。 -/
theorem perfectPrismVarpi_pow (W : OrientedPrism p A)
    (hW : W.deltaStructure.IsPerfect) :
    perfectPrismVarpi W hW ^ p = (p : A ⧸ W.ideal) *
      (-Ideal.Quotient.mk W.ideal (W.deltaStructure.delta (perfectPrismVarpiLift W hW))) := by
  have h := congrArg (Ideal.Quotient.mk W.ideal) (perfectPrismVarpiLift_frobenius W hW)
  rw [W.deltaStructure.frobeniusLift_apply, map_add, map_pow, map_mul, map_natCast] at h
  have hd : Ideal.Quotient.mk W.ideal W.generator = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  rw [hd] at h
  change perfectPrismVarpi W hW ^ p + _ = 0 at h
  linear_combination h

/-- 概要：ϖ の p 乗と p は同じ主イデアルを生成する。
方針：明示的な積公式と δ(x) の単元性を使う。
規約：R の p ねじれの有無を仮定しない。
使われ方：BS Rem 7.15（著者版 p.62）の ϖ の条件。 -/
theorem perfectPrismVarpi_span_pow (W : OrientedPrism p A)
    (hW : W.deltaStructure.IsPerfect) :
    Ideal.span {perfectPrismVarpi W hW ^ p} = Ideal.span {(p : A ⧸ W.ideal)} := by
  rw [perfectPrismVarpi_pow]
  exact Ideal.span_singleton_mul_right_unit
    (((perfectPrismVarpiLift_delta_isUnit W hW).map (Ideal.Quotient.mk W.ideal)).neg) _

/-- 概要：distinguished 元 x について (φ(x),x)=(p,x)。
方針：φ(x)−x^p=pδ(x) と単元 δ(x) による主イデアルの不変性を使う。
規約：δ 環の完全性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の二つの係数商の比較。 -/
theorem distinguished_frobenius_pair_span (D : DeltaStructure p A) (x : A)
    (hx : IsUnit (D.delta x)) :
    Ideal.span {D.frobeniusLift x, x} = Ideal.span {(p : A), x} := by
  have hpow : x ^ p = x * x ^ (p - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (Nat.Prime.one_le (Fact.out : p.Prime))]
  rw [D.frobeniusLift_apply, hpow, Ideal.span_pair_right_mul_add,
    Ideal.span_insert, Ideal.span_insert,
    Ideal.span_singleton_mul_right_unit hx]

/-- 概要：prism 生成元と ϖ の持上げの二元イデアルは (p,x)。
方針：逆 Frobenius 像が distinguished であることを一般 δ 計算へ適用する。
規約：等式は A のイデアルとして述べる。
使われ方：BS Rem 7.15（著者版 p.62）の R/ϖ の実係数商。 -/
theorem perfectPrismVarpiLift_pair_span (W : OrientedPrism p A)
    (hW : W.deltaStructure.IsPerfect) :
    Ideal.span {W.generator, perfectPrismVarpiLift W hW} =
      Ideal.span {(p : A), perfectPrismVarpiLift W hW} := by
  rw [← perfectPrismVarpiLift_frobenius W hW]
  exact distinguished_frobenius_pair_span _ _ (perfectPrismVarpiLift_delta_isUnit W hW)

/-- 概要：主イデアルによる二重商を二元イデアルによる商と同一視する。
方針：二重商の標準同型と主イデアルの像の公式を使う。
規約：元の環の代表元を保つ同型を選ぶ。
使われ方：BS Rem 7.15（著者版 p.62）の係数商比較。 -/
def principalDoubleQuotEquiv (a b : A) :
    ((A ⧸ Ideal.span {a}) ⧸ Ideal.span {Ideal.Quotient.mk (Ideal.span {a}) b}) ≃+*
      A ⧸ Ideal.span {a, b} :=
  ((Ideal.quotEquivOfEq (show
      Ideal.span {Ideal.Quotient.mk (Ideal.span {a}) b} =
        (Ideal.span {b}).map (Ideal.Quotient.mk (Ideal.span {a})) by
      rw [Ideal.map_span, Set.image_singleton])).trans
    (DoubleQuot.quotQuotEquivQuotSup (Ideal.span {a}) (Ideal.span {b}))).trans
      (Ideal.quotEquivOfEq (Ideal.span_insert a {b}).symm)

/-- 概要：主イデアル二重商の同型は同じ代表元を送る。
方針：標準二重商同型の計算規則を使う。
規約：元は元の環 A で指定する。
使われ方：BS Rem 7.15（著者版 p.62）の係数射の照合。 -/
theorem principalDoubleQuotEquiv_mk (a b t : A) :
    principalDoubleQuotEquiv a b (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ t)) =
      Ideal.Quotient.mk _ t := by
  simp only [principalDoubleQuotEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  rw [show Ideal.Quotient.mk _ (Ideal.Quotient.mk _ t) =
    DoubleQuot.quotQuotMk (Ideal.span {a}) (Ideal.span {b}) t from rfl,
    DoubleQuot.quotQuotEquivQuotSup_quotQuotMk, Ideal.quotEquivOfEq_mk]

/-- 概要：prism 商の ϖ 還元は A/p の x 還元と環同型。
方針：両二重商を (d,x)=(p,x) による商へ写す。
規約：x は指定生成元の Frobenius 逆像。正則性は仮定しない。
使われ方：BS Rem 7.15（著者版 p.62）の R/ϖ 係数。 -/
def perfectPrismVarpiQuotientEquiv (W : OrientedPrism p A)
    (hW : W.deltaStructure.IsPerfect) :
    ((A ⧸ W.ideal) ⧸ Ideal.span {perfectPrismVarpi W hW}) ≃+*
      ((A ⧸ Ideal.span {(p : A)}) ⧸
        Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : A)}) (perfectPrismVarpiLift W hW)}) :=
  ((principalDoubleQuotEquiv W.generator (perfectPrismVarpiLift W hW)).trans
    (Ideal.quotEquivOfEq (perfectPrismVarpiLift_pair_span W hW))).trans
      (principalDoubleQuotEquiv (p : A) (perfectPrismVarpiLift W hW)).symm

/-- 概要：係数商同型は A から来る代表元を保つ。
方針：二重商同型の代表元公式を両側で使う。
規約：同型の向きは R/ϖ から (A/p)/(x)。
使われ方：BS Rem 7.15（著者版 p.62）の多項式係数比較。 -/
theorem perfectPrismVarpiQuotientEquiv_mk (W : OrientedPrism p A)
    (hW : W.deltaStructure.IsPerfect) (t : A) :
    perfectPrismVarpiQuotientEquiv W hW (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ t)) =
      Ideal.Quotient.mk _ (Ideal.Quotient.mk _ t) := by
  apply (principalDoubleQuotEquiv (p : A) (perfectPrismVarpiLift W hW)).injective
  simp only [perfectPrismVarpiQuotientEquiv, RingEquiv.trans_apply,
    RingEquiv.apply_symm_apply, principalDoubleQuotEquiv_mk]
  change (Ideal.quotEquivOfEq _)
    ((principalDoubleQuotEquiv W.generator (perfectPrismVarpiLift W hW))
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ t))) = _
  rw [principalDoubleQuotEquiv_mk, Ideal.quotEquivOfEq_mk]

end SerrePositivity.BhattScholze.Andre
