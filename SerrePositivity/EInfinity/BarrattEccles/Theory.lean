module

public import SerrePositivity.EInfinity.Interface.Core
public import SerrePositivity.EInfinity.BarrattEccles.CAlgDiscreteUnderRecognition
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeDerivedFreeForget

/-!
# Barratt–Eccles 模型の中核

## 概要
既存の CAlg_R を HA §3.1・§3.2.2 に対応する中核に代入する。

## 方針
既存の忘却、指定極限の保存、離散代数との比較を使う。

## 規約
既存の CAlg_R と同じ関手・同じ指定錐を保持する。

## 使われ方
BS 著者版 Proposition 8.5 の CAlg 版と D(R) 版の接続。
-/

@[expose] public noncomputable section

universe u

open CategoryTheory SSet
open SerrePositivity.InfinityCategories

namespace SerrePositivity.EInfinity.BarrattEccles

attribute [local instance] HasDerivedCategory.standard

/-- HA §3.2.2 に対応する証明済みの Barratt–Eccles 中核。 -/
def barrattEcclesCore : EInfinityCore.{u} where
  CAlg S := CAlg_R S
  quasicategory S := cAlg_R_quasicategory S
  forget S := cAlgForgetDerived S
  forget_preservesLimits S _ _ _ c hc := cAlgForgetDerived_mapJoinCone_isLimit S c hc
  discrete S := discreteCAlgUnderEmbedding S
  discrete_forget S := discreteCAlgUnderEmbedding_forgetIso S
  discrete_recognition S _ x := cAlgUnderlyingDisc_iff_discreteUnder S x

end SerrePositivity.EInfinity.BarrattEccles
