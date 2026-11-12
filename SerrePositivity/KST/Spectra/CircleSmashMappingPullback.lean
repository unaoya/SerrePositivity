module

public import SerrePositivity.KST.Spectra.CircleSmashTriangles
public import SerrePositivity.KST.Spectra.CofiberMappingPullback
public import SerrePositivity.KST.Spectra.TriangleDiskCellIso

/-!
概要：二つの円の smash 積の写像空間は二つの相対三角形の写像空間の pullback。
方針：厳密な点つき pushout に反変内部 Hom を適用する。
規約：相対三角形の対角辺への制限が共通の底となる。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。二重 loop の変数交換の比較。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：円の smash 積の写像空間を相対三角形の写像空間の pullback として表す。
方針：対角辺での貼り合わせの反対に極限保存の Hom 関手を適用する。
規約：標的の Kan 性はこの厳密な同定には不要。
使われ方：Goerss–Jardine I §7、HTT A.3.3。二つの三角形の交換による逆元の計算。 -/
theorem circleSmashMapping_isPullback (Y : PointedSimplicialSet.{u}) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre circleSmashUpper Y)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre circleSmashLower Y)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre triangleDiskDiagonal Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre triangleDiskDiagonal Y) := by
  have h := (circleSmashTriangles_isPushout.op.flip).map (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.cofiberMappingFunctor Y)
  simpa only [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.cofiberMappingFunctor_map] using h

/-- 概要：二重円の写像を上側の相対三角形へ制限する射は Kan fibration。
方針：対角辺への制限の fibration を pullback に沿って引き戻す。
規約：標的 Y の Kan 性だけを使う。
使われ方：Kerodon §3.1.3（Tag 00TJ）、Goerss–Jardine I §7。貼り合わせの交換を fiber の成分へ移す。 -/
instance circleSmashUpper_restriction_fibration (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] : Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre circleSmashUpper Y) := by
  have hf : Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre triangleDiskDiagonal Y) :=
    triangleDisk_restriction_fibration Y
  apply (fibration_iff _).2
  exact J.rlp.of_isPullback (circleSmashMapping_isPullback Y).flip
    ((fibration_iff _).1 hf)

end

end SerrePositivity.KST.Spectra
