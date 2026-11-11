module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PairUnitHomRestriction
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
概要：元の全単位族の固定左制限と、保存条件で制限した固定左 coslice の厳密な比較。
方針：二つの引き戻しの貼り合わせを、同じ LR 合成の等式で接続する。
規約：元の右関手圏を底に保持する。
使われ方：固定左の普遍単位による単位空間の表現可能性。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：固定左 coslice を元の全右保存関手圏へ制限した空間。
方針：元の固定左射影を e1 の右包含で引き戻す。
規約：非可逆な自然変換を含む底を使う。
使われ方：既存の普遍単位の分類との比較。 -/
def PreservingLeftUnitCoslice {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) : SSet.{u + 1} :=
  pullback (pullback.snd
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C.obj))))
    ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor v)).app C.obj)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightFunctorInclusion D C)

/-- 概要：固定左の保存関手上の単位空間から元の右関手圏への射影。
方針：同じ引き戻しの第二脚を取る。
規約：底の全自然変換を保持する。
使われ方：分類関手の共通の底。 -/
def preservingLeftUnitProjection {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) : PreservingLeftUnitCoslice v ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C :=
  pullback.snd _ _

instance preservingLeftUnitProjection_leftFibration {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (preservingLeftUnitProjection v) := by
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C.obj)))
  let f := (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor v)).app C.obj
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.snd p f) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))⟩
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := pullback.snd p f))⟩

instance preservingLeftUnitCoslice_quasicategory {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) : Quasicategory (PreservingLeftUnitCoslice v) :=
  quasicategory_of_innerFibration (preservingLeftUnitProjection v)

/-- 概要：元の単位族を固定左へ引き戻すと、保存条件付きの同じ coslice と厳密に同型。
方針：引き戻しを二通りに貼り合わせ、固定左の実合成の等式で中間項を同定する。
規約：元の単体集合の同型を使う。
使われ方：単位族の分類と普遍単位の比較。 -/
def pairFixedLeftCosliceIso {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) :
    pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.covariantPairUnitProjection C D) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairFixedLeftBase v) ≅
      PreservingLeftUnitCoslice v :=
  pullbackLeftPullbackSndIso _ _ _ ≪≫
    pullback.congrHom rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairFixedLeftBase_composition v) ≪≫
      (pullbackLeftPullbackSndIso _ _ _).symm

/-- 概要：厳密な固定左比較は元の右保存関手を保持する。
方針：三つの引き戻し同型の第二脚の計算則を使う。
規約：同じ底上の射の等式。
使われ方：分類関手の比較を元の底上で行う。 -/
lemma pairFixedLeftCosliceIso_projection {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) :
    (pairFixedLeftCosliceIso v).hom ≫ preservingLeftUnitProjection v =
      pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.covariantPairUnitProjection C D) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairFixedLeftBase v) := by
  simp [pairFixedLeftCosliceIso, preservingLeftUnitProjection, pullback.congrHom_hom,
    Category.assoc]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
