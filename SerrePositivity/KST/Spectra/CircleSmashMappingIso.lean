module

public import SerrePositivity.KST.Spectra.CircleSmashMappingPullback
public import SerrePositivity.KST.Spectra.CircleSmashSwap
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SelfPullbackInverseEdge

/-!
概要：二重円の写像空間と自己 pullback の同型は変数交換と両因子の交換を結ぶ。
方針：写像空間の pullback の同型の二つの射影で計算する。
規約：基礎単体集合の厳密な同型。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。一般の自己 pullback の交換の式への接続。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：二重円の写像空間と対角辺への制限の自己 pullback の厳密な同型。
方針：写像空間の pullback 表示の標準の同型を使う。
規約：二つの射影は上側と下側への制限となる。
使われ方：Kerodon §3.2.3（Tag 00W3）。三角形の交換の一般的な自己 pullback 模型への移送。 -/
def circleSmashMappingPairIso (Y : PointedSimplicialSet.{u}) :
    (PointedObject.basedHom circleSmashSquare.{u} Y).right ≅
      pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre triangleDiskDiagonal Y)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre triangleDiskDiagonal Y) :=
  (circleSmashMapping_isPullback Y).isoPullback

/-- 概要：二重円の写像空間の交換は同型の下で自己 pullback の両因子の交換となる。
方針：二つの三角形への制限で、smash の交換が両包含を交換する式を使う。
規約：実際の単体集合の射の等式。
使われ方：Goerss–Jardine I §7。変数交換の成分での符号の計算。 -/
theorem circleSmashMappingPairIso_swap (Y : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (PointedObject.smashSwap PointedSimplicialSet.circle.{u}
      PointedSimplicialSet.circle.{u}) Y ≫ (circleSmashMappingPairIso Y).hom =
      (circleSmashMappingPairIso Y).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackSwap (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre triangleDiskDiagonal Y) := by
  dsimp only [circleSmashMappingPairIso]
  apply pullback.hom_ext
  · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackSwap, Category.assoc, pullback.lift_fst]
    rw [(circleSmashMapping_isPullback Y).isoPullback_hom_fst,
      (circleSmashMapping_isPullback Y).isoPullback_hom_snd]
    simpa only [← op_comp, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.cofiberMappingFunctor_map, circleSmashUpper_swap] using
      ((_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.cofiberMappingFunctor Y).map_comp
        (PointedObject.smashSwap PointedSimplicialSet.circle.{u}
          PointedSimplicialSet.circle.{u}).op circleSmashUpper.op).symm
  · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackSwap, Category.assoc, pullback.lift_snd]
    rw [(circleSmashMapping_isPullback Y).isoPullback_hom_snd,
      (circleSmashMapping_isPullback Y).isoPullback_hom_fst]
    simpa only [← op_comp, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.cofiberMappingFunctor_map, circleSmashLower_swap] using
      ((_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.cofiberMappingFunctor Y).map_comp
        (PointedObject.smashSwap PointedSimplicialSet.circle.{u}
          PointedSimplicialSet.circle.{u}).op circleSmashLower.op).symm

end

end SerrePositivity.KST.Spectra
