module

public import SerrePositivity.BhattScholze.Inputs.PerfectoidizationInterface
public import SerrePositivity.BhattScholze.PerfectoidizationInterface.IntegralExistence
public import SerrePositivity.CommutativeAlgebra.IntegralPerfectoid
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-! # 整代数の普遍 perfectoid 化（界面から導出した定理）

従来 BS Thm 1.17(1) を直接引用していた公開入口である。
現在は導来 perfectoid 化界面の存在だけを引用し、integral と universal から導く。
公開名・型と、非完備を含む任意の整代数という範囲を保つ。
-/

public section
universe u
namespace SerrePositivity.BhattScholze.Inputs

/--
## 概要
BS Thm 1.17(1) の存在命題を、E3 界面から導出した定理。

## 方針
界面の存在を取り出し、Π2-6 の integral → 離散性 → universal の証明へ渡す。
integral の原典は Thm 10.11、離散時 universal の原典は Cor 8.14 である。

## 規約
この公開入口は以前 Thm 1.17(1) の文献入力であったが、現在は直接の未証明箇所を持たない。
有限性・有限表示性・有界 p 冪ねじれ・S の完備性は追加しない。
原典：https://people.mpim-bonn.mpg.de/scholze/prisms.pdf 。

## 使われ方
既存の同じ公開名・型で整代数の普遍 perfectoid 化を供給する。
-/
theorem exists_perfectoidization_of_integral
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) :
    ∃ (C : Type u) (_ : CommRing C) (f : S →+* C), IsPerfectoidization p f := by
  exact PerfectoidizationInterface.exists_perfectoidization_of_integral R S p hR
    (Classical.choice (exists_perfectoidizationInterfaceE3 R p hR))

end SerrePositivity.BhattScholze.Inputs
