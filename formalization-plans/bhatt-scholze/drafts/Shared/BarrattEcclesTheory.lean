-- BS-W14 D72。実例の未供給欄の作業用。BS の drafts からは import しない。
module

public import SerrePositivity.EInfinity.BarrattEccles.Theory
public import SerrePositivity.EInfinity.BarrattEccles.CAlgAlgebraSource
public import SerrePositivity.EInfinity.BarrattEccles.OperadAugmentation
public import SerrePositivity.EInfinity.ComplexLimits.OrdinaryDerivedSource
public import SerrePositivity.EInfinity.Interface.Theory
public import SerrePositivity.EInfinity.Operad.CommutativeAlgebraFunctor

/-!
# Barratt–Eccles 模型の全界面の残り

## 概要
HA §3.2.2–3.2.4 と DAG XIII Construction 2.2.6 の未供給欄を記録する。

## 方針
証明済みの中核を使い、厳密な cdga 入力を operad augmentation に沿って読む。

## 規約
この実例は drafts に置く。sorry のある欄は作業の所在を示す。

## 使われ方
BS 著者版 Definition 8.2、Lemma 8.4 ほかで使う全界面の実例。
-/

@[expose] public noncomputable section

universe u

open CategoryTheory SSet
open SerrePositivity.InfinityCategories

namespace SerrePositivity.EInfinity.BarrattEccles

attribute [local instance] HasDerivedCategory.standard

/-- BS-W14 D72 の全欄の実例案。残りの比較は各欄のコメントに記す。 -/
def barrattEcclesTheory : EInfinityTheory.{u} where
  toEInfinityCore := barrattEcclesCore
  forget_conservative := by sorry -- CAlg 側で U が同値を反映
  forget_preservesSifted := by sorry -- HA 3.2.3.1
  presentable := by sorry -- HA 3.2.3.5
  coprodWith := by sorry -- 指定した右因子との余積関手
  coprodWith_cocone := by sorry -- 各頂点で同じ余積関手の指定錐
  coproduct_tensor := by sorry -- HA 3.2.4.7 の自然比較
  discrete_initial := by sorry -- 基底環自身の離散像が始対象
  coproduct_tensor_legs := by sorry -- 指定二脚を単位からの標準テンソル射へ送る
  restrictD := by sorry -- M13 の D 側
  restrictD_id := by sorry
  restrictD_comp := by sorry
  restrictD_homologyIso := by sorry -- M13 の係数制限に対する自然比較
  restrict := by sorry -- M13 の CAlg 側
  baseChange := by sorry
  baseChange_adjunction := by sorry
  restrict_forget := by sorry
  baseChange_forget := by sorry
  restrict_id := by sorry
  restrict_comp := by sorry
  discrete_restrict := by sorry -- 離散代数についての全関手比較
  pi0 := by sorry -- 既存の代表上の H⁰ をホモトピー圏の関手にする
  pi0_forget := by sorry
  pi0_discrete := by sorry
  pi0_restrict := by sorry
  strictToD S _ := ComplexLimits.complexOrdinaryDerivedSource S
  strictToD_homologyIso := by
    sorry -- complexSemifreeResolutionAugmentationHomotopy をホモロジーに移す。
          -- 成分を complexSemifreeResolutionValueAugmentation の Hⁱ と照合する
  ofCosimplicial := by sorry -- 交代余面複体上の E∞ 実現
  ofCosimplicial_forget := by sorry
  ofCosimplicial_cone := by sorry
  ofCosimplicial_restrict := by sorry
  ofCdga S _ :=
    nerveMap (commutativeAlgebraFunctor S ⋙ Operad.restrictAlgebra (augmentation S)) ≫
      algebraCAlgSource S
  ofCdga_forget := by sorry -- algebraCAlgSource_underlyingDerivedIso と厳密忘却の比較
  ofCdga_discrete := by sorry -- 零次の cdga と discreteCAlgUnderEmbedding の比較
  ofCosimplicialCdga := by sorry
  ofCosimplicialCdga_cone := by sorry
  ofCosimplicialCdga_discrete := by sorry
  ofCosimplicialCdga_evalZero := by sorry
  ofCosimplicialCdga_evalZero_leg := by sorry -- 同じ指定錐の [0] の脚
  powerOp0 := by sorry -- DAG XIII Construction 2.2.6
  powerOp0_zero := by sorry
  powerOp0_pos := by sorry
  powerOp0_discrete := by sorry
  powerOp0_tot := by sorry

end SerrePositivity.EInfinity.BarrattEccles
