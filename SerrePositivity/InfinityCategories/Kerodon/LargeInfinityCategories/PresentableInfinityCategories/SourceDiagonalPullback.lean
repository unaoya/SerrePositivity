module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PullbackRightComposition
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.NativeCartesianFibrationPreservation

/-!
概要：二段の left fibration を、底変換した二つの全空間と対角切断の引き戻しで表す。
方針：元の射の graph と二つの引き戻し射影で普遍性を検証する。
規約：全単体集合の引き戻しであり、fiber ごとの比較に置き換えない。
使われ方：固定始域 coslice 内の compact 性を底の二つの共変 Hom から検出する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：相対的な二つの終点を、元の射により同じ底上へ送る。
方針：合成に沿う引き戻し比較を使う。
規約：第一射影は厳密に保持する。
使われ方：coslice の全写像空間の引き戻し。 -/
def sourceDiagonalComparison {Z D C : SSet.{u}} (q : Z ⟶ D) (d : D ⟶ C) :
    pullback d (q ≫ d) ⟶ pullback d d :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.pullbackMapRightOfComp d d (q ≫ d) q rfl

/-- 概要：同じ終点を二つ並べる元の対角切断。
方針：恒等射二本を引き戻しへ持ち上げる。
規約：底を厳密に保つ。
使われ方：元の coslice 点の構造射を固定する。 -/
def sourceDiagonal {D C : SSet.{u}} (d : D ⟶ C) : D ⟶ pullback d d :=
  pullback.lift (𝟙 D) (𝟙 D) rfl

/-- 概要：元の射と元の全空間を同時に保持する graph。
方針：元の射と恒等射を引き戻しへ持ち上げる。
規約：第二射影は恒等射。
使われ方：対角切断に沿った元の全空間の回収。 -/
def sourceDiagonalGraph {Z D C : SSet.{u}} (q : Z ⟶ D) (d : D ⟶ C) :
    Z ⟶ pullback d (q ≫ d) :=
  pullback.lift q (𝟙 Z) (by rw [Category.id_comp])

/-- 概要：対角切断に沿う引き戻しは元の全空間そのもの。
方針：各射影の等式で graph の唯一性と存在を検証する。
規約：元の関手 q を第二脚に保持する。
使われ方：全分類図式に対する引き戻し保存判定。 -/
lemma sourceDiagonalGraph_isPullback {Z D C : SSet.{u}} (q : Z ⟶ D) (d : D ⟶ C) :
    IsPullback (sourceDiagonalGraph q d) q (sourceDiagonalComparison q d) (sourceDiagonal d) := by
  have hfst : sourceDiagonalGraph q d ≫ pullback.fst d (q ≫ d) = q :=
    pullback.lift_fst _ _ _
  have hsnd : sourceDiagonalGraph q d ≫ pullback.snd d (q ≫ d) = 𝟙 Z :=
    pullback.lift_snd _ _ _
  have hmapfst : sourceDiagonalComparison q d ≫ pullback.fst d d =
      pullback.fst d (q ≫ d) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.pullbackMapRightOfComp_fst _ _ _ _ _
  have hmapsnd : sourceDiagonalComparison q d ≫ pullback.snd d d =
      pullback.snd d (q ≫ d) ≫ q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.pullbackMapRightOfComp_snd _ _ _ _ _
  have hdiagfst : sourceDiagonal d ≫ pullback.fst d d = 𝟙 D := pullback.lift_fst _ _ _
  have hdiagsnd : sourceDiagonal d ≫ pullback.snd d d = 𝟙 D := pullback.lift_snd _ _ _
  refine IsPullback.mk' ?_ ?_ ?_
  · apply pullback.hom_ext
    · rw [Category.assoc, hmapfst, hfst, Category.assoc, hdiagfst, Category.comp_id]
    · rw [Category.assoc, hmapsnd, ← Category.assoc, hsnd, Category.id_comp,
        Category.assoc, hdiagsnd, Category.comp_id]
  · intro W a b hab _
    have h := congrArg (fun k ↦ k ≫ pullback.snd d (q ≫ d)) hab
    simpa only [Category.assoc, hsnd, Category.comp_id] using h
  · intro W a b hab
    have hf := congrArg (fun k ↦ k ≫ pullback.fst d d) hab
    have hs := congrArg (fun k ↦ k ≫ pullback.snd d d) hab
    simp only [Category.assoc, hmapfst, hdiagfst, Category.comp_id] at hf
    simp only [Category.assoc, hmapsnd, hdiagsnd, Category.comp_id] at hs
    refine ⟨a ≫ pullback.snd d (q ≫ d), ?_, hs⟩
    apply pullback.hom_ext
    · rw [Category.assoc, hfst]
      exact hs.trans hf.symm
    · rw [Category.assoc, hsnd, Category.comp_id]

/-- 概要：対角比較は元の left fibration の底変換。
方針：合成に沿う比較の引き戻し表示を使う。
規約：追加の fibrancy 仮定は不要。
使われ方：全分類図式の引き戻し判定の入力。 -/
lemma sourceDiagonalComparison_leftFibration {Z D C : SSet.{u}}
    (q : Z ⟶ D) (d : D ⟶ C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (sourceDiagonalComparison q d) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.of_isPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.pullbackMapRightOfComp_isPullback d d (q ≫ d) q rfl)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := q))⟩

/-- 概要：二つの底変換分類と一点分類の保存性は、元の相対分類へ移る。
方針：元の graph の引き戻し正方形に全分類図式の保存判定を適用する。
規約：小さい試験添字と元の全空間を保持する。
使われ方：coslice 内の compact 性の三つの分類入力への分解。 -/
lemma sourceDiagonalClassification_preservesKappaFilteredColimits
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ)
    {Z D C : SSet.{u + 1}} [Quasicategory D]
    (q : Z ⟶ D) (d : D ⟶ C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration d]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (q ≫ d)]
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits.{u, u + 1} μ
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram (pullback.fst d (q ≫ d))))
    (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits.{u, u + 1} μ
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram (𝟙 D)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits.{u, u + 1} μ
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram (pullback.fst d d))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits.{u, u + 1} μ
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram q) := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (sourceDiagonalComparison q d) :=
    sourceDiagonalComparison_leftFibration q d
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.cartesianFibrationClassification_preservesKappaFilteredColimits h
    (sourceDiagonalGraph q d) q (sourceDiagonalComparison q d) (sourceDiagonal d)
    (sourceDiagonalGraph_isPullback q d) q (pullback.fst d (q ≫ d)) (𝟙 D)
    (pullback.fst d d) (pullback.lift_fst _ _ _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.pullbackMapRightOfComp_fst _ _ _ _ _) (pullback.lift_fst _ _ _) he hd hb

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
