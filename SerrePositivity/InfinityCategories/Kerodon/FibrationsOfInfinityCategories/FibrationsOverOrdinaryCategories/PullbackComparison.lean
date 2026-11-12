module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.FiniteComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.OverPullbackMorphism

/-!
概要：有限鎖への引き戻しでの cocartesian scaffold の比較。
方針：simplicial replacement の底変換の厳密な pullback 同型で、有限鎖上の比較と同定する。
規約：局所性判定では pullback の底を第一成分、元の全空間を第二成分とする。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、有限鎖の帰納から任意の底への局所的比較。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：scaffold の底変換は、Over 圏での比較の pullback と二つの標準同型で一致する。
方針：pullback の両射影へ合成し、replacement の底変換と元の比較の式を照合する。
規約：元の射影の可換性 h を Over 圏の射の条件に用いる。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、各単体での比較射の同定。 -/
lemma F1B.cocartesianScaffoldBaseChange_overPullbackMap
    {C D : Type u} [Category.{u} C] [Category.{u} D] {E : SSet.{u}}
    (p : E ⟶ nerve C) (F : C ⥤ SSet.{u}) (l : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F ⟶ E)
    (h : l ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F) (H : D ⥤ C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementBaseMap_isPullback H F).flip.isoPullback.hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMap
          (Over.homMk (U := Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F)) (V := Over.mk p) l h)
          (Over.mk (nerveMap H)) ≫
          (pullbackSymmetry (nerveMap H) p).hom = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftScaffoldBaseChange p F l h H := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackSymmetry_hom_comp_fst,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMap, Over.mk_hom, pullback.lift_snd, IsPullback.isoPullback_hom_snd_assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftScaffoldBaseChange, pullback.lift_fst, Over.homMk_left]
  · simp only [Category.assoc, pullbackSymmetry_hom_comp_snd,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMap, Over.mk_hom, pullback.lift_fst, IsPullback.isoPullback_hom_fst,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftScaffoldBaseChange, pullback.lift_snd]

/-- 概要：cocartesian scaffold の比較を空でない有限鎖へ引き戻すと前合成同値を得る。
方針：引き戻した scaffold に有限鎖上の比較定理を適用し、標準同型を消去する。
規約：通常の圏の任意の関手 H による底変換を扱う。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、局所性の仮定となる有限鎖上の同値。 -/
lemma CocartesianScaffold.overPullback_finiteComparison
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
    (F : C ⥤ SSet.{u}) [∀ c, Quasicategory (F.obj c)]
    (l : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F ⟶ E) (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.CocartesianScaffold p F l)
    (h : l ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F)
    (n : ℕ) (H : ULift.{u} (Fin (n + 1)) ⥤ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMap
          (Over.homMk (U := Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F)) (V := Over.mk p) l h)
          (Over.mk (nerveMap H))) := by
  have (c : ULift.{u} (Fin (n + 1))) : Quasicategory ((H ⋙ F).obj c) :=
    inferInstanceAs (Quasicategory (F.obj (H.obj c)))
  have hb := hs.baseChange H
  have hc := hb.finiteComparison n _ _ _
  have he := F1B.cocartesianScaffoldBaseChange_overPullbackMap p F l h H
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftScaffoldBaseChange p F l h H) at hc
  rw [← he] at hc
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementBaseMap_isPullback H F).flip.isoPullback).cancel_left
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (pullbackSymmetry (nerveMap H) p)).cancel_right hc)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
