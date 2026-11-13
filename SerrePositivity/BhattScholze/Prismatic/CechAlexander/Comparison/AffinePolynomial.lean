module

public import SerrePositivity.BhattScholze.Prismatic.Site.PrismOver
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.KoszulModel
public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# affine 模型の完備多項式環

## 概要
向き付き prism の剰余環上の多項式を p 進完備化する。

## 方針
一座標 Koszul 完備化の零次ホモロジーと、その標準射を用いる。

## 規約
Čech–Alexander 模型の基底としては有限変数の場合を使う。

## 使われ方
小さい affine 模型とその濃度の上限。
-/

@[expose] public section
noncomputable section

universe u v

open SerrePositivity.DerivedCompletion

namespace SerrePositivity.BhattScholze.Prismatic

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)

/-- prism の剰余環上の p 進完備多項式環。 -/
abbrev prismPolynomialCompletion (T : Type v) :=
  PrincipalCompletionH0 (MvPolynomial T (A ⧸ P.ideal)) (p : MvPolynomial T (A ⧸ P.ideal))

/-- 剰余環上の完備多項式環の可換環構造。 -/
instance prismPolynomialRing (T : Type v) : CommRing (prismPolynomialCompletion P T) :=
  principalCompletionCommRing _ _

/-- 多項式環から完備多項式環への標準射。 -/
def prismPolynomialUnit (T : Type v) :
    MvPolynomial T (A ⧸ P.ideal) →+* prismPolynomialCompletion P T :=
  principalCompletionUnitRingHom _ _

/-- 係数の剰余環からの標準射による代数構造。 -/
instance prismPolynomialAlgebra (T : Type v) : Algebra (A ⧸ P.ideal) (prismPolynomialCompletion P T) :=
  ((prismPolynomialUnit P T).comp MvPolynomial.C).toAlgebra

/-- r 変数の場合の完備多項式環。 -/
abbrev polyCompletion (r : ℕ) := prismPolynomialCompletion P (Fin r)

/-- r 変数の完備多項式環が定める濃度の上限。 -/
abbrev polyCutoff (r : ℕ) := cutoff A (polyCompletion P r)

end SerrePositivity.BhattScholze.Prismatic
