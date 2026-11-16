module

public import SerrePositivity.EInfinity.BarrattEccles.SourceRightConeNaturality
public import SerrePositivity.EInfinity.BarrattEccles.RightSimplicialConeSource
public import SerrePositivity.EInfinity.BarrattEccles.ConstantDiagramSourceFunctor

/-!
# 具体的な両 frame の錐比較の始域自然性

概要：BM 命題 4.1・Hovey §5.4 の同じ両錐比較は始域の射にも自然。
方針：同じ frame 射・試験始域の射・augmentation の四角形を混合 Hom へ移す。
規約：元の代数の cofibrancy と単体集合モデルを入力にしない。
使われ方：図式の局所化 Hom と計算対象への Hom の始域自然性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits _root_.HomotopicalAlgebra
open SerrePositivity.Reedy
open SerrePositivity.DiagramModel.WeightedCones
open _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame

attribute [local implicit_reducible] CofibrantResolutionFamily.atObject

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：具体的な始域・右 frame の錐比較は始域の射に自然（Hovey §5.4）。
方針：混合 Hom の二つの厳密な可換四角形と右錐表示の自然性を合成する。
規約：試験始域の前合成も元の始域の同じ射から関手的に作る。
使われ方：π₀ の二つの局所化 Hom 比較を始域にも自然にする。 -/
lemma sourceRightConeComparisonIso_source {Y Z : (operad A).Algebra} (f : Y ⟶ Z)
    (F : K ⥤ (operad A).Algebra) {D : Type v} [Category.{w} D] (L : SSet.{u} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    L.map ((constantDiagramSourceMap A K ((framedLimitProbeFunctor A).map f)).app F) ≫
        (sourceRightConeComparisonIso A K Y F L hL).hom =
      (sourceRightConeComparisonIso A K Z F L hL).hom ≫
        L.map ((framedLimitConeSourceMap A K f).app F) := by
  let := modelCategory A
  let q := cosimplicialResolutionFamily (mappingCofibrantFactorization A)
  let P := framedLimitProbeFunctor A
  let B (X : (operad A).Algebra) := q.obj.obj (P.obj X)
  let a (X : (operad A).Algebra) := q.augmentation.app (P.obj X)
  let R := F ⋙ rightSimplicialFrameFamily A
  let b := Functor.whiskerLeft F (rightSimplicialFrameAugmentation A)
  have hc (X : (operad A).Algebra) : IsCofibrant (P.obj X) := framedLimitProbe_cofibrant A X
  let l (X : (operad A).Algebra) := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.leftDiagramComparison K (B X) F R b
  let r (X : (operad A).Algebra) := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.rightDiagramComparison K (B X) (a X) R
  have hleft X := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.leftDiagram_kanComplex K (B X) (q.cofibrant _)
    (q.atObject _).homotopicallyConstant F (fun k => isFibrant A (F.obj k))
  have hright X := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.rightDiagram_kanComplex K (P.obj X) R
    (fun k => rightSimplicialFrame_cofibrant A (F.obj k))
    (fun k _ _ g => rightSimplicialFrame_homotopicallyConstant A (F.obj k) g)
  have hl X := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.leftDiagramComparison_isIso K (B X) (q.cofibrant _) F R b
    (fun k => isFibrant A (F.obj k)) (fun k n => rightSimplicialFrame_fibrant A (F.obj k) n)
    (fun k n => rightSimplicialFrameAugmentation_quasiIso A (F.obj k) n)
  have hr X := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.rightDiagramComparison_isIso K (B X) (q.cofibrant _) (a X)
    (q.atObject _).augmentation_weakEquivalence R
    (fun k => rightSimplicialFrame_cofibrant A (F.obj k))
  let T := coneSpace K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)
  let e X := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.kanConeComparisonIso K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight_cofibrant K) L hL (l X) (r X) (hleft X) (hright X) (hl X) (hr X)
  let g := q.obj.map (P.map f)
  let s := Functor.whiskerLeft F (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap g)
  let t := rightSimplicialHomSourceMap A K f F
  let c := Functor.whiskerLeft R (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame.mixedSourceMap g)
  have hn : L.map (T.map s) ≫ (e Y).hom = (e Z).hom ≫ L.map (T.map t) :=
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.kanConeComparisonIso_naturality K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)
      (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight_cofibrant K) L hL (l Z) (r Z) (l Y) (r Y)
      (hleft Z) (hright Z) (hleft Y) (hright Y) (hl Z) (hr Z) (hl Y) (hr Y) s t c
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame.leftDiagramComparison_source K g F R b)
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame.rightDiagramComparison_source K g (P.map f) (a Y) (a Z)
        (q.augmentation.naturality (P.map f)) R)
  have hnright : L.map (T.map t) ≫ L.map (rightSimplicialConeIso A K Y F).hom =
      L.map (rightSimplicialConeIso A K Z F).hom ≫
        L.map ((framedLimitConeSourceMap A K f).app F) := by
    rw [← L.map_comp, rightSimplicialConeIso_source, L.map_comp]
  change L.map (T.map s) ≫ ((e Y).hom ≫ L.map (rightSimplicialConeIso A K Y F).hom) =
    ((e Z).hom ≫ L.map (rightSimplicialConeIso A K Z F).hom) ≫
      L.map ((framedLimitConeSourceMap A K f).app F)
  rw [← Category.assoc, hn, Category.assoc, hnright, ← Category.assoc]

/-- 概要：両錐比較の逆も元の始域の前合成に自然（Hovey §5.4）。
方針：同じ比較の順方向の四角形に二つの逆を合成する。
規約：既存の比較同型の同じ逆を使う。
使われ方：右錐から始域錐へ戻す π₀ 比較の自然性。 -/
lemma sourceRightConeComparisonIso_source_inv {Y Z : (operad A).Algebra} (f : Y ⟶ Z)
    (F : K ⥤ (operad A).Algebra) {D : Type v} [Category.{w} D] (L : SSet.{u} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    L.map ((framedLimitConeSourceMap A K f).app F) ≫
        (sourceRightConeComparisonIso A K Y F L hL).inv =
      (sourceRightConeComparisonIso A K Z F L hL).inv ≫
        L.map ((constantDiagramSourceMap A K ((framedLimitProbeFunctor A).map f)).app F) := by
  apply (cancel_epi (sourceRightConeComparisonIso A K Z F L hL).hom).mp
  rw [← Category.assoc, ← sourceRightConeComparisonIso_source, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

end SerrePositivity.EInfinity.BarrattEccles
