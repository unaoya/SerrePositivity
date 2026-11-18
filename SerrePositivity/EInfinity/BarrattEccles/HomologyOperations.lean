module

public import SerrePositivity.EInfinity.BarrattEccles.HomologyCoefficient
public import SerrePositivity.HomologicalAlgebra.Complexes.HomologyZero.PairingLinear

/-!
# E 代数の実際の H⁰ の積と単位の元

概要：BF §1 の E の零次演算から、実際の H⁰ の双線形積と単位の候補を構成する。
方針：arity 2 と arity 0 の収縮の切断を代数作用へ入力する。
規約：H⁰ の型と加群構造は元の homology 0。環公理は後続で検証する。
使われ方：E2a-4 の H⁰ の可換環構造。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

/-- 概要：選んだ零次係数の E 代数の n 入力作用（BF §1）。
方針：単位を付け、収縮の切断を代数作用の係数へ入力する。
規約：arity 零も含み、底の実際の複体射として構成する。
使われ方：H⁰ の積・単位・結合則の比較。 -/
def homologyOperation (X : (operad A).Algebra) (n : ℕ) : power X.carrier n ⟶ X.carrier :=
  (λ_ (power X.carrier n)).inv ≫ (aritySection A n ▷ power X.carrier n) ≫ X.action n

/-- 概要：arity 2 の作用を二因子の通常のテンソルの射にする（BF §1）。
方針：一入力テンソル冪の余分な単位を挿入する。
規約：実際の Koszul テンソルを使う。
使われ方：H⁰ の双線形積の定義。 -/
def homologyBinary (X : (operad A).Algebra) : X.carrier ⊗ X.carrier ⟶ X.carrier :=
  (X.carrier ◁ (oneIso X.carrier).inv) ≫ homologyOperation X 2

/-- 概要：E 代数の実際の H⁰ の双線形積（BF §1）。
方針：arity 2 の複体射を代表元独立な H⁰ の作用へ移す。
規約：元の homology 0 の A 加群構造を使う。
使われ方：H⁰ の可換環構造と分配法則。 -/
def homologyProduct (X : (operad A).Algebra) :
    X.carrier.homology 0 →ₗ[A] X.carrier.homology 0 →ₗ[A] X.carrier.homology 0 :=
  _root_.SerrePositivity.HomologyZero.pairing (homologyBinary X)

/-- 概要：E 代数の H⁰ の単位の候補となる元（BF §1）。
方針：arity 零の作用を単位からの射として H⁰ の類へ送る。
規約：実際の nullary 演算を使う。
使われ方：H⁰ の環の単位と単位則。 -/
def homologyOne (X : (operad A).Algebra) : X.carrier.homology 0 :=
  _root_.SerrePositivity.HomologyZero.unitClass X.carrier (homologyOperation X 0)

end SerrePositivity.EInfinity.BarrattEccles
