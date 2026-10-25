module

public import SerrePositivity.BhattScholze.Andre.OrdinaryMonicRoot
public import SerrePositivity.BhattScholze.Andre.Remark715.PrincipalDPFree

/-!
# André E1：モニック関係式の分冪表示環の忠実平坦性

## 概要

標数 p の係数環 R と正次数モニック f に対し、一変数多項式環内の f の分冪表示環は
元の係数環 R 上忠実平坦である。有限段の変数置換 `Y = Z^n` にも適用する。
BS 著者版 Rem 7.15(1)（p.62）の通常の平坦性の計算に対応する。

## 方針

`R[Y]/(f^p)` のモニック剰余による忠実平坦性と、既存の分冪表示環のこの商上の
忠実平坦性を合成する。元の R の係数作用と整合するスカラー塔を明示する。

## 規約

既存の `PrincipalDPPresentation` を対象とする。実 prismatic envelope の Frobenius
引戻しとの同定は別工程であり、この結果だけで最終目標の忠実平坦性を結論しない。
原典の Prop 7.10 による cover 性を引用せず通常代数の計算を行う経路である。

## 使われ方

Rem 7.15 の pd 計算のうち、有限段の剰余環の忠実平坦性に用いる。
-/

@[expose] public noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

open Polynomial

/-- 概要：標数 p の係数環上のモニック関係の分冪表示環は元の係数環上自由。
方針：f の p 乗のモニック剰余基底と、その商上の分冪表示環の自由性を合成する。
規約：自由性だけには正次数は不要。実 prismatic envelope との同定を含まない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の自由性の有限段。 -/
theorem monicDPPresentation_free
    {R : Type u} [CommRing R] (p : ℕ) (hprime : p.Prime) (hp : (p : R) = 0)
    (f : R[X]) (hf : f.Monic) :
    Module.Free R (PrincipalDPPresentation R[X] f) := by
  have hpP : (p : R[X]) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg (C : R →+* R[X]) hp
  let := principalDPQuotientAlgebra hprime.pos hpP f
  let := principalDPQuotient_isScalarTower_base (A := R) hprime.pos hpP f
  let : Module.Free R (R[X] ⧸ Ideal.span {f ^ p}) := (hf.pow p).free_adjoinRoot
  let := principalDPPresentation_quotient_free p hprime hpP f
  exact Module.Free.trans (R := R) (S := R[X] ⧸ Ideal.span {f ^ p})
    (M := PrincipalDPPresentation R[X] f)

/-- 概要：標数 p の一般基底に対し、商の忠実平坦性は分冪表示環の忠実平坦性を与える。
方針：商上の既存の忠実平坦性と、元の基底作用を保つスカラー塔を使って合成する。
規約：分冪表示環と実 prismatic envelope の同定は要求しない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の pd 計算を元の基底へ移す。 -/
theorem principalDPPresentation_faithfullyFlat_of_quotient
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (p : ℕ) (hprime : p.Prime) (hp : (p : B) = 0) (y : B)
    (hQ : Module.FaithfullyFlat R (B ⧸ Ideal.span {y ^ p})) :
    Module.FaithfullyFlat R (PrincipalDPPresentation B y) := by
  let := principalDPQuotientAlgebra hprime.pos hp y
  let := principalDPQuotient_isScalarTower_base (A := R) hprime.pos hp y
  let := principalDPQuotient_moduleFaithfullyFlat hprime hp y
  let := hQ
  exact Module.FaithfullyFlat.trans R (B ⧸ Ideal.span {y ^ p}) (PrincipalDPPresentation B y)

/-- 概要：標数 p の任意可換環上の正次数モニックの分冪表示環は元の係数環上忠実平坦。
方針：f の p 乗のモニック性と正次数で通常商の忠実平坦性を供給する。
規約：係数環の非零性は不要である。
使われ方：BS Rem 7.15(1)（著者版 p.62）のモニック関係の有限段の計算。 -/
theorem monicDPPresentation_faithfullyFlat
    {R : Type u} [CommRing R] (p : ℕ) (hprime : p.Prime) (hp : (p : R) = 0)
    (f : R[X]) (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    Module.FaithfullyFlat R (PrincipalDPPresentation R[X] f) := by
  have hpP : (p : R[X]) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg (C : R →+* R[X]) hp
  apply principalDPPresentation_faithfullyFlat_of_quotient p hprime hpP f
  exact adjoinRoot_faithfullyFlat (f ^ p) (hf.pow p) (by
    rw [hf.natDegree_pow]
    exact Nat.mul_pos hprime.pos hdeg)

/-- 概要：正の有限段 `Y = Z^n` におけるモニック関係の分冪表示環も忠実平坦。
方針：expand のモニック性と次数公式を前定理に適用する。
規約：有限段の結果であり、有向余極限や完備化後の結果ではない。
使われ方：BS Rem 7.15（著者版 p.62）の無限 p 冪根多項式環に至る有限段。 -/
theorem expandedMonicDPPresentation_faithfullyFlat
    {R : Type u} [CommRing R] (p : ℕ) (hprime : p.Prime) (hp : (p : R) = 0)
    (f : R[X]) (hf : f.Monic) (hdeg : 0 < f.natDegree) (n : ℕ) (hn : 0 < n) :
    Module.FaithfullyFlat R (PrincipalDPPresentation R[X] (expand R n f)) := by
  apply monicDPPresentation_faithfullyFlat p hprime hp _ (hf.expand hn)
  rw [natDegree_expand]
  exact Nat.mul_pos hdeg hn

end SerrePositivity.BhattScholze.Andre
