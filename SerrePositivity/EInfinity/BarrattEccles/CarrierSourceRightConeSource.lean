module

public import SerrePositivity.EInfinity.BarrattEccles.CarrierSourceRightConeNaturality
public import SerrePositivity.EInfinity.BarrattEccles.CarrierRightSimplicialConeSource
public import SerrePositivity.EInfinity.BarrattEccles.CarrierConstantDiagramSourceFunctor

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

open CategoryTheory Limits HomotopicalAlgebra
open SerrePositivity.DifferentialGraded
open SerrePositivity.Reedy
open SerrePositivity.DiagramModel.WeightedCones
open SerrePositivity.EInfinity.FrameHom.MixedFrame

attribute [local implicit_reducible] CofibrantResolutionFamily.atObject

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：具体的な始域・右 frame の錐比較は始域の射に自然（Hovey §5.4）。
方針：混合 Hom の二つの厳密な可換四角形と右錐表示の自然性を合成する。
規約：試験始域の前合成も元の始域の同じ射から関手的に作る。
使われ方：π₀ の二つの局所化 Hom 比較を始域にも自然にする。 -/
lemma carrierSourceRightConeComparisonIso_source {Y Z : Complex A} (f : Y ⟶ Z)
    (F : K ⥤ (operad A).Algebra) {D : Type v} [Category.{w} D] (L : SSet.{u} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    L.map ((CarrierDiagram.constantDiagramSourceMap A K
      ((carrierFramedLimitProbeFunctor A).map f)).app
      ((Diagram.forget A K).obj F)) ≫
        (carrierSourceRightConeComparisonIso A K Y F L hL).hom =
      (carrierSourceRightConeComparisonIso A K Z F L hL).hom ≫
        L.map ((carrierFramedLimitConeSourceMap A K f).app F) := by
  let := projectiveModelCategory A
  let q := cosimplicialResolutionFamily (carrierProbeFactorization A)
  let P := carrierFramedLimitProbeFunctor A
  let B (X : Complex A) := q.obj.obj (P.obj X)
  let a (X : Complex A) := q.augmentation.app (P.obj X)
  let R := F ⋙ carrierRightSimplicialFrameFamily A
  let b := Functor.whiskerLeft F (carrierRightSimplicialFrameAugmentation A)
  have hc (X : Complex A) : IsCofibrant (P.obj X) := carrierFramedLimitProbe_cofibrant A X
  let l (X : Complex A) := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.leftDiagramComparison K (B X) ((Diagram.forget A K).obj F) R b
  let r (X : Complex A) := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.rightDiagramComparison K (B X) (a X) R
  have hleft X := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.leftDiagram_kanComplex K (B X) (q.cofibrant _)
    (q.atObject _).homotopicallyConstant ((Diagram.forget A K).obj F)
      (fun k => CarrierDiagram.complex_isFibrant A (F.obj k).carrier)
  have hright X := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.rightDiagram_kanComplex K (P.obj X) R
    (fun k => carrierRightSimplicialFrame_cofibrant A (F.obj k))
    (fun k _ _ g => carrierRightSimplicialFrame_homotopicallyConstant A (F.obj k) g)
  have hl X := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.leftDiagramComparison_isIso K (B X) (q.cofibrant _) ((Diagram.forget A K).obj F) R b
    (fun k => CarrierDiagram.complex_isFibrant A (F.obj k).carrier)
    (fun k n => carrierRightSimplicialFrame_fibrant A (F.obj k) n)
    (fun k n => carrierRightSimplicialFrameAugmentation_quasiIso A (F.obj k) n)
  have hr X := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.rightDiagramComparison_isIso K (B X) (q.cofibrant _) (a X)
    (q.atObject _).augmentation_weakEquivalence R
    (fun k => carrierRightSimplicialFrame_cofibrant A (F.obj k))
  let T := coneSpace K (HomotopyWeight.weight K)
  let e X := HomotopyWeight.kanConeComparisonIso K (HomotopyWeight.weight K)
    (HomotopyWeight.weight_cofibrant K) L hL (l X) (r X) (hleft X) (hright X) (hl X) (hr X)
  let g := q.obj.map (P.map f)
  let s := Functor.whiskerLeft ((Diagram.forget A K).obj F) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap g)
  let t := carrierRightSimplicialHomSourceMap A K f F
  let c := Functor.whiskerLeft R (mixedSourceMap g)
  have hn : L.map (T.map s) ≫ (e Y).hom = (e Z).hom ≫ L.map (T.map t) :=
    HomotopyWeight.kanConeComparisonIso_naturality K (HomotopyWeight.weight K)
      (HomotopyWeight.weight_cofibrant K) L hL (l Z) (r Z) (l Y) (r Y)
      (hleft Z) (hright Z) (hleft Y) (hright Y) (hl Z) (hr Z) (hl Y) (hr Y) s t c
      (leftDiagramComparison_source K g ((Diagram.forget A K).obj F) R b)
      (rightDiagramComparison_source K g (P.map f) (a Y) (a Z)
        (q.augmentation.naturality (P.map f)) R)
  have hnright : L.map (T.map t) ≫ L.map (carrierRightSimplicialConeIso A K Y F).hom =
      L.map (carrierRightSimplicialConeIso A K Z F).hom ≫
        L.map ((carrierFramedLimitConeSourceMap A K f).app F) := by
    rw [← L.map_comp, carrierRightSimplicialConeIso_source, L.map_comp]
  change L.map (T.map s) ≫ ((e Y).hom ≫ L.map (carrierRightSimplicialConeIso A K Y F).hom) =
    ((e Z).hom ≫ L.map (carrierRightSimplicialConeIso A K Z F).hom) ≫
      L.map ((carrierFramedLimitConeSourceMap A K f).app F)
  rw [← Category.assoc, hn, Category.assoc, hnright, ← Category.assoc]

/-- 概要：両錐比較の逆も元の始域の前合成に自然（Hovey §5.4）。
方針：同じ比較の順方向の四角形に二つの逆を合成する。
規約：既存の比較同型の同じ逆を使う。
使われ方：右錐から始域錐へ戻す π₀ 比較の自然性。 -/
lemma carrierSourceRightConeComparisonIso_source_inv {Y Z : Complex A} (f : Y ⟶ Z)
    (F : K ⥤ (operad A).Algebra) {D : Type v} [Category.{w} D] (L : SSet.{u} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    L.map ((carrierFramedLimitConeSourceMap A K f).app F) ≫
        (carrierSourceRightConeComparisonIso A K Y F L hL).inv =
      (carrierSourceRightConeComparisonIso A K Z F L hL).inv ≫
        L.map ((CarrierDiagram.constantDiagramSourceMap A K
      ((carrierFramedLimitProbeFunctor A).map f)).app
      ((Diagram.forget A K).obj F)) := by
  apply (cancel_epi (carrierSourceRightConeComparisonIso A K Z F L hL).hom).mp
  rw [← Category.assoc, ← carrierSourceRightConeComparisonIso_source, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

end SerrePositivity.EInfinity.BarrattEccles
