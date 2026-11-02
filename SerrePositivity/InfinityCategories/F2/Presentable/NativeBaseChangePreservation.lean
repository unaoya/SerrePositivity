module

public import SerrePositivity.InfinityCategories.F2.Presentable.NativeUniverseContinuity
public import SerrePositivity.InfinityCategories.F1.Compact.ClassificationTransport

/-!
概要：底変換した left fibration の分類へ、小さい filtered 余極限保存を移す。
方針：元の分類の全底変換比較と、二つの射影の対称同型を使う。
規約：分類される全空間を選び直さず、小さい試験添字を保持する。
使われ方：固定始域 coslice の Hom の対角引き戻し。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：第二射影で表した底変換の分類は、元の二つの保存性から保存的。
方針：宇宙を分離した合成と全底変換同型を使う。
規約：全小余極限保存は要求しない。
使われ方：compact な像からの Hom に限らない分類の底変換。 -/
lemma leftClassification_baseChange_preservesKappaFilteredColimits
    {μ : Cardinal.{u}} {E B D : SSet.{u + 1}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) [LeftFibration p] (G : D ⟶ B)
    (hG : IsKappaAccessibleFunctor μ G)
    (hp : Compact.PreservesKappaFilteredColimits.{u, u + 1} μ
      (leftStraighteningInfinityDiagram p)) :
    Compact.PreservesKappaFilteredColimits.{u, u + 1} μ
      (leftStraighteningInfinityDiagram (pullback.snd p G)) :=
  (hG.comp_universe hp).of_functorIso (leftStraighteningInfinityDiagram_baseChangeIso p G)

/-- 概要：第一射影で表した同じ底変換の分類も filtered 余極限を保存する。
方針：二つの射影を全空間の対称同型で比較する。
規約：第一射影自体の分類を結論する。
使われ方：元の graph の引き戻しの二つの分類成分。 -/
lemma leftClassification_baseChange_fst_preservesKappaFilteredColimits
    {μ : Cardinal.{u}} {E B D : SSet.{u + 1}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) [LeftFibration p] (G : D ⟶ B)
    (hG : IsKappaAccessibleFunctor μ G)
    (hp : Compact.PreservesKappaFilteredColimits.{u, u + 1} μ
      (leftStraighteningInfinityDiagram p)) :
    Compact.PreservesKappaFilteredColimits.{u, u + 1} μ
      (leftStraighteningInfinityDiagram (pullback.fst G p)) := by
  have h := leftClassification_baseChange_preservesKappaFilteredColimits p G hG hp
  exact h.of_functorIso (Compact.leftClassification_overIso
    (pullback.fst G p) (pullback.snd p G) (pullbackSymmetry G p)
    (pullbackSymmetry_hom_comp_snd G p)).symm

end SerrePositivity.InfinityCategories.F2.Presentable
