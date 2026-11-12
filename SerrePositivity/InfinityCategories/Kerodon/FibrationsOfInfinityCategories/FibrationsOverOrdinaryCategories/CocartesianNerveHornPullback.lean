module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.SubcomplexInverseImageComparison

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ReplacementInnerHorn
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ArbitraryBaseChange

/-!
概要：strict replacement の内ホーンの逆像の比較を実際の cocartesian fibration へ移す。
方針：scaffold 比較とその底変換の同値性を二対三則で消去する。
規約：内ホーン自体は quasicategory と仮定しない。
使われ方：Kerodon Lemma 5.3.6.6（Tag 02RK）、表現空間の inner anodyne 制限。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：replacement の部分底への制限が前合成同値なら実際の cocartesian fibration の制限も同値。
方針：universal scaffold の元の比較と底変換した比較を消去する。
規約：部分底 A は任意の単体集合の部分複体でよい。
使われ方：Kerodon §5.3.6（Tag 037W）、strict な模型からの内ホーンの逆像の比較。 -/
lemma cocartesianFibration_subcomplex_pullback_isPrecompositionEquivalence_of_replacement
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (A : (nerve C).Subcomplex)
    (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence
      (pullback.snd A.ι
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram p)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (pullback.snd A.ι p) := by
  have h := hA.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianUniversalScaffold_isPrecompositionEquivalence p)
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMap_snd
    (Over.homMk
      (U := Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram p)))
      (V := Over.mk p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianUniversalScaffold p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianUniversalScaffold_projection p)) (Over.mk A.ι)
  change _ ≫ pullback.snd A.ι p =
    pullback.snd A.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram p)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianUniversalScaffold p at he
  rw [← he] at h
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianUniversalScaffold_overPullback_isPrecompositionEquivalence p A.ι).cancel_left h

/-- 概要：有限鎖の nerve 上の cocartesian fibration の内ホーンの逆像の射影は前合成同値。
方針：replacement の逆像の inner anodyne 性を scaffold で移す。
規約：全空間の小ささ以外の追加の選択や同値仮定を要求しない。
使われ方：Kerodon Lemma 5.3.6.6（Tag 02RK） の生成ホーンの場合。 -/
lemma cocartesianFibration_nerveHorn_pullback_isPrecompositionEquivalence (n : ℕ)
    (k : Fin (n + 1)) (h0 : 0 < k) (hn : k < Fin.last n) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 1)))) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.replacementNerveHorn n k).ι p) := by
  apply cocartesianFibration_subcomplex_pullback_isPrecompositionEquivalence_of_replacement p
  apply _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isPrecompositionEquivalence_pullback_snd_of_subcomplexInverseImage
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_of_innerAnodyne _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.replacementNerveHorn_preimage_innerAnodyne n k h0 hn (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram p))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
