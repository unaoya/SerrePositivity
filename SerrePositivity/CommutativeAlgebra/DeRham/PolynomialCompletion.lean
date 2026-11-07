module

public import SerrePositivity.CommutativeAlgebra.DeRham.Polynomial
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.KoszulModel

/-!
# 多項式の完備微分形式

## 概要
多項式環を p 進完備化し、係数拡大した微分形式を作る。

## 方針
完備多項式環は一座標 Koszul 完備化の零次ホモロジーを使う。

## 規約
形式の係数のみを完備化し、外冪の次数を保つ。

## 使われ方
Hodge–Tate 写像の定義域と、多項式の Čech–Alexander 模型の基底。
-/

@[expose] public section
noncomputable section

universe u

open scoped TensorProduct
open SerrePositivity.DerivedCompletion

namespace SerrePositivity.DeRham

/-- p 進完備多項式環の台。 -/
abbrev completedPoly (k : Type u) [CommRing k] (T : Type u) [Fintype T] [DecidableEq T]
    (p : ℕ) : Type u :=
  PrincipalCompletionH0 (Poly k T) (p : Poly k T)

variable (k : Type u) [CommRing k] (T : Type u) [Fintype T] [DecidableEq T] (p : ℕ)

/-- p 進完備多項式環の環構造。 -/
instance completedPolyRing : CommRing (completedPoly k T p) :=
  principalCompletionCommRing _ _

/-- 完備化単位による多項式代数構造。 -/
instance completedPolyAlgebra : Algebra (Poly k T) (completedPoly k T p) :=
  principalCompletionAlgebra _ _

/-- 基底環から完備多項式環への代数構造。 -/
instance completedPolyBaseAlgebra : Algebra k (completedPoly k T p) :=
  ((principalCompletionUnitRingHom (Poly k T) (p : Poly k T)).comp MvPolynomial.C).toAlgebra

/-- 基底環、多項式環、完備多項式環の係数拡大は推移的。 -/
instance completedPoly_isScalarTower : IsScalarTower k (Poly k T) (completedPoly k T p) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- 概要：完備化した多項式代数の微分形式。
方針：多項式形式の係数を完備多項式環に拡大する。
規約：i は外冪の次数。
使われ方：完備 de Rham 複体と Hodge–Tate 比較。 -/
abbrev completedForms (i : ℕ) := completedPoly k T p ⊗[Poly k T] forms k T i

/-- 完備化単位は多項式形式を係数 1 の純テンソルに写す。 -/
def completedFormsUnit (i : ℕ) : forms k T i →+ completedForms k T p i :=
  (TensorProduct.mk (Poly k T) (completedPoly k T p) (forms k T i) 1).toAddMonoidHom

end SerrePositivity.DeRham
