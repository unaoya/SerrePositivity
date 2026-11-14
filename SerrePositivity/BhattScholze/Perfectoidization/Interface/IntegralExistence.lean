module
public import SerrePositivity.BhattScholze.Perfectoidization.Interface.InitialBridge
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.InitialValueCone

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.InitialCofinality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeEdgeCompatibility
public import SerrePositivity.BhattScholze.Perfectoidization.Interface.Derived
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.DiscreteCharacterization
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import SerrePositivity.BhattScholze.Inputs.PerfectoidizationInterface
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Defs
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Completion
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# 整代数と有限代数の普遍 perfectoid 化の存在

導来 perfectoid 化の界面から整代数の普遍環を取り出し、公開入口と完備化への比較を与える。始対象の一般計算と指定単位の比較は別の二つのモジュールに分離する。
-/

universe u v w



@[expose] public section IntegralExistence

namespace SerrePositivity.BhattScholze.PerfectoidizationInterface

/-- 整代数の普遍 perfectoid 化は、導来 perfectoid 化の界面の integral と universal の欄から従う
（BS 著者版 Theorem 10.11 と Corollary 8.14 の環としての帰結、序論の Theorem 1.17 (1)）。 -/
theorem exists_perfectoidization_of_integral
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (F : PerfectoidizationInterfaceE3 R p hR) :
    ∃ (C : Type u) (_ : CommRing C) (f : S →+* C), IsPerfectoidization p f := by
  have hInt : (letI : Algebra R (ofAlgebra R S).right := (ofAlgebra R S).hom.hom.toAlgebra
      Algebra.IsIntegral R (ofAlgebra R S).right) := by
    change @Algebra.IsIntegral R S _ _ (algebraMap R S).toAlgebra
    rw [toAlgebra_algebraMap]
    infer_instance
  exact ⟨(F.h0.ringFunctor.obj (ofAlgebra R S)).right, inferInstance,
    (F.h0.unit.app (ofAlgebra R S)).right.hom,
    F.universal (ofAlgebra R S) (F.integral (ofAlgebra R S) hInt).1⟩

end SerrePositivity.BhattScholze.PerfectoidizationInterface

end IntegralExistence

/-! ## 整代数の普遍 perfectoid 化（界面から導出した定理）

従来 BS 著者版 Theorem 1.17(1) を直接引用していた公開入口である。
現在は導来 perfectoid 化界面の存在だけを引用し、integral と universal から導く。
公開名・型と、非完備を含む任意の整代数という範囲を保つ。
-/

public section IntegralPerfectoidization

namespace SerrePositivity.BhattScholze.Inputs

/--
## 概要
BS 著者版 Theorem 1.17(1) の存在命題を、導来 perfectoid 化の界面から導出した定理。

## 方針
界面の存在を取り出し、整代数の離散性と普遍性 の integral → 離散性 → universal の証明へ渡す。
integral の原典は BS 著者版 Theorem 10.11、離散時 universal の原典は BS 著者版 Corollary 8.14 である。

## 規約
この公開入口は以前 BS 著者版 Theorem 1.17(1) の文献入力であったが、現在は直接の未証明箇所を持たない。
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

end IntegralPerfectoidization

/-! ## 整代数の原典入力から有限版と完備化版への接続

有限代数の整性を確認して原典の普遍 perfectoid 化を適用する。
完備化の場合には、同じ目標環と写像の一意延長を用いて普遍性を移す。
新しい対象を選び直さず、古典完備化と導来完備化の同値も仮定しない。
-/

@[expose] public section FiniteIntegralExistence

namespace SerrePositivity.BhattScholze

/-- 有限代数の存在主張は、整代数についての原典の存在入力への適用である。
有限表示性はこの導出には不要である。 -/
theorem exists_perfectoidization_of_finite
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) :
    ∃ (C : Type u) (_ : CommRing C) (f : S →+* C), IsPerfectoidization p f :=
  Inputs.exists_perfectoidization_of_integral R S p hR

/-- 整代数の古典 p 進完備化にも、同じ環を使って普遍 perfectoid 化を与えられる。
元環の普遍性と完備化への一意延長からの系であり、prismatic perfection 本体の定義ではない。 -/
theorem exists_perfectoidization_of_completed_integral
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) :
    ∃ (C : Type u) (_ : CommRing C)
      (f : AdicCompletion (Ideal.span {(p : S)}) S →+* C), IsPerfectoidization p f := by
  obtain ⟨C, hC, f, hf⟩ := Inputs.exists_perfectoidization_of_integral R S p hR
  exact ⟨C, hC, hf.completionMap p, hf.to_completion p⟩

end SerrePositivity.BhattScholze

end FiniteIntegralExistence
