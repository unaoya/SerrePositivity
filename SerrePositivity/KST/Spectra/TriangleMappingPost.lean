module

public import SerrePositivity.KST.Spectra.CircleSmashMappingIso
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SelfPullbackNaturality

/-!
概要：三角形による写像空間の pullback 同型は標的の写像について自然。
方針：内部 Hom の源の制限の自然性を二つの射影で確認する。
規約：標的の射に同型性を要求しない。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。loop の符号反転の自己 pullback への作用。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：点つき写像空間の源の制限と標的の後合成は可換。
方針：閉構造の pre の自然性を基礎単体集合へ送る。
規約：源と標的の射は任意。
使われ方：Goerss–Jardine I §7。対角辺への制限の可換四角形。 -/
theorem PointedMapping.pre_post_comm {A B Y Z : PointedSimplicialSet.{u}}
    (i : A ⟶ B) (v : Y ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i Y ≫ (PointedObject.basedHomMap A v).right =
      (PointedObject.basedHomMap B v).right ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i Z := by
  have h := ((MonoidalClosed.pre i).naturality v).symm
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at h
  exact congrArg Under.Hom.right h

/-- 概要：三角形の写像空間による自己 pullback 同型は標的の写像と可換。
方針：両射影における包含への制限と後合成の可換性を使う。
規約：Kan 性は不要。
使われ方：Kerodon §3.2.3（Tag 00W3）。二重円の交換と標的の loop の逆元の比較。 -/
theorem circleSmashMappingPairIso_post {Y Z : PointedSimplicialSet.{u}} (v : Y ⟶ Z) :
    (PointedObject.basedHomMap circleSmashSquare v).right ≫
        (circleSmashMappingPairIso Z).hom =
      (circleSmashMappingPairIso Y).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackMap (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre triangleDiskDiagonal Y)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre triangleDiskDiagonal Z)
          (PointedObject.basedHomMap triangleDisk v).right
          (PointedObject.basedHomMap PointedSimplicialSet.circle v).right
          (PointedMapping.pre_post_comm triangleDiskDiagonal v) := by
  dsimp only [circleSmashMappingPairIso]
  apply pullback.hom_ext
  · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackMap, Category.assoc, pullback.lift_fst,
      (circleSmashMapping_isPullback Z).isoPullback_hom_fst]
    rw [← Category.assoc, (circleSmashMapping_isPullback Y).isoPullback_hom_fst]
    exact (PointedMapping.pre_post_comm circleSmashUpper v).symm
  · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackMap, Category.assoc, pullback.lift_snd,
      (circleSmashMapping_isPullback Z).isoPullback_hom_snd]
    rw [← Category.assoc, (circleSmashMapping_isPullback Y).isoPullback_hom_snd]
    exact (PointedMapping.pre_post_comm circleSmashLower v).symm

end

end SerrePositivity.KST.Spectra
