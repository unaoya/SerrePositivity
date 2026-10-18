module

public import SerrePositivity.BhattScholze.PerfectoidizationInterface.ExcisionDiagram

/-! # D(R) 上の perfectoid 化界面（E3）の型

概要：原典の各性質を、その根拠を導出するためのデータとともに束ねる。
方針：界面の型だけを宣言し、存在は主張しない。
規約：普遍性は離散時の環準同型の普遍性。全射性や Tor 消滅を欄に含めない。
使われ方：Π2-5 以降で既存の二入力を界面依存の定理として導く。
-/

@[expose] public section
universe u
namespace SerrePositivity.BhattScholze.PerfectoidizationInterface
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.InfinityCategories SerrePositivity.DerivedCompletion
open scoped Simplicial

/-- 原典と照合した E3 の型。界面の存在を追加の公理として宣言しない。 -/
structure PerfectoidizationInterfaceE3 (R : Type u) [CommRing R]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) where
  /-- 通常の Type u の代数を底の導来対象に送る関手。 -/
  perfd : algebraNerve R ⟶ derivedInfinityCategory R
  /-- 元の離散代数からのホモトピー整合的な単位。 -/
  unit : NatInfinity R (J R) perfd
  /-- H⁰ の環構造と、単位・射のコホモロジーとの整合性。 -/
  h0 : H0RingData R perfd unit
  /-- cochain の負次数が消える。離散性より弱い条件。 -/
  coconnective : ∀ S (i : ℤ), i < 0 → IsZero (H R i (vertex R perfd S))
  /-- 離散な場合だけ、指定した環の単位が perfectoid 化になる。 -/
  universal : ∀ S, Disc R (vertex R perfd S) →
    IsPerfectoidization p (h0.unit.app S).right.hom
  /-- Type u の標的を添字とする、元の単位付きの指定錐。 -/
  limitCone : ∀ S, BSLimitConeData R p perfd unit h0 S
  /-- 指定した錐の極限性。一般の巨大極限の存在は要求しない。 -/
  limit_isLimit : ∀ S, IsLimitCone (limitCone S).cone
  /-- 任意の整代数の離散性と perfectoid 性。非完備な始域も含む。 -/
  integral : ∀ (S : A_R R),
    (letI : Algebra R S.right := S.hom.hom.toAlgebra; Algebra.IsIntegral R S.right) →
    Disc R (vertex R perfd S) ∧ IsIntegralPerfectoid (h0.ringFunctor.obj S).right p
  /-- 通常の商の指定四角形が、底の導来 ∞ 圏で引き戻しになる。 -/
  excision : ∀ {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right),
    IsModuleComplete S.right (p : S.right) (ModuleCat.of S.right S.right) →
    IsModuleComplete T.right (p : T.right) (ModuleCat.of T.right T.right) →
    IsModuleComplete S.right (p : S.right) (ModuleCat.of S.right I) →
    ArcOutside R p f I → IsPullbackSquare (perfdSquare R perfd f I)

end SerrePositivity.BhattScholze.PerfectoidizationInterface
