module

public import SerrePositivity.EInfinity.BarrattEccles.CarrierSourceRightConeComparison

/-!
# 具体的な両 frame の錐比較の終域自然性

概要：BM 命題 4.1・Hovey §5.4 の両錐比較を元の図式の関手同型へ束ねる。
方針：同じ augmentation の自然性から混合 Hom の二つの可換四角形を作る。
規約：既存の carrierSourceRightConeComparisonIso の同じ成分を使う。
使われ方：定値図式と実際の極限計算関手の導来随伴の自然性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits _root_.HomotopicalAlgebra
open SerrePositivity.DifferentialGraded
open SerrePositivity.Reedy
open SerrePositivity.DiagramModel.WeightedCones
open _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame

attribute [local implicit_reducible] CofibrantResolutionFamily.atObject

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：始域・右 frame の具体的な錐比較は終域図式に自然（Hovey §5.4）。
方針：両比較の自然な可換四角形と右錐の添字移送同型を合成する。
規約：元の代数に cofibrancy は要求せず、任意の anodyne 反転先を許す。
使われ方：π₀ の局所化 Hom 比較の後合成との両立。 -/
def carrierSourceRightConeComparisonNatIso (Y : Complex A)
    {D : Type v} [Category.{w} D] (L : SSet.{u} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    Diagram.forget A K ⋙
        CarrierDiagram.constantDiagramSourceHom A K (carrierFramedLimitProbe A Y) ⋙ L ≅
      carrierFramedLimitConeSpace A K Y ⋙ L := by
  let := projectiveModelCategory A
  let q := cosimplicialResolutionFamily (carrierProbeFactorization A)
  let B := q.obj.obj (carrierFramedLimitProbe A Y)
  let a := q.augmentation.app (carrierFramedLimitProbe A Y)
  have := carrierFramedLimitProbe_cofibrant A Y
  let R (F : K ⥤ (operad A).Algebra) := F ⋙ carrierRightSimplicialFrameFamily A
  let b (F : K ⥤ (operad A).Algebra) :=
    Functor.whiskerLeft F (carrierRightSimplicialFrameAugmentation A)
  let e (F : K ⥤ (operad A).Algebra) := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.mixedConeComparisonIso K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight_cofibrant K) B (q.cofibrant _)
    (q.atObject _).homotopicallyConstant a (q.atObject _).augmentation_weakEquivalence
    ((Diagram.forget A K).obj F) (R F) (b F)
    (fun k => CarrierDiagram.complex_isFibrant A (F.obj k).carrier)
    (fun k n => carrierRightSimplicialFrame_fibrant A (F.obj k) n)
    (fun k n => carrierRightSimplicialFrameAugmentation_quasiIso A (F.obj k) n)
    (fun k => carrierRightSimplicialFrame_cofibrant A (F.obj k))
    (fun k _ _ f => carrierRightSimplicialFrame_homotopicallyConstant A (F.obj k) f) L hL
  let E : Diagram.forget A K ⋙
      CarrierDiagram.constantDiagramSourceHom A K (carrierFramedLimitProbe A Y) ⋙ L ≅
      carrierRightSimplicialHomFamily A K Y ⋙ coneSpace K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) ⋙ L :=
    NatIso.ofComponents e (by
      intro F G f
      let s := Functor.whiskerRight ((Diagram.forget A K).map f) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom B)
      let r := Functor.whiskerRight f (carrierRightSimplicialFrameFamily A)
      let t := Functor.whiskerRight r (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame.rightHomFunctor (carrierFramedLimitProbe A Y))
      let c := Functor.whiskerRight r (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame.mixedFunctor B)
      change L.map ((coneSpace K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)).map s) ≫ (e G).hom =
        (e F).hom ≫ L.map ((coneSpace K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)).map t)
      apply _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.kanConeComparisonIso_naturality K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)
        (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight_cofibrant K) L hL (c := c)
      case hF =>
        exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.leftDiagram_kanComplex K B (q.cofibrant _)
          (q.atObject _).homotopicallyConstant ((Diagram.forget A K).obj F)
            (fun k => CarrierDiagram.complex_isFibrant A (F.obj k).carrier)
      case hG =>
        exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.rightDiagram_kanComplex K _ (R F)
          (fun k => carrierRightSimplicialFrame_cofibrant A (F.obj k))
          (fun k _ _ g => carrierRightSimplicialFrame_homotopicallyConstant A (F.obj k) g)
      case hF' =>
        exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.leftDiagram_kanComplex K B (q.cofibrant _)
          (q.atObject _).homotopicallyConstant ((Diagram.forget A K).obj G)
            (fun k => CarrierDiagram.complex_isFibrant A (G.obj k).carrier)
      case hG' =>
        exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.rightDiagram_kanComplex K _ (R G)
          (fun k => carrierRightSimplicialFrame_cofibrant A (G.obj k))
          (fun k _ _ g => carrierRightSimplicialFrame_homotopicallyConstant A (G.obj k) g)
      case hf =>
        exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.leftDiagramComparison_isIso K B (q.cofibrant _)
          ((Diagram.forget A K).obj F) (R F) (b F)
          (fun k => CarrierDiagram.complex_isFibrant A (F.obj k).carrier)
          (fun k n => carrierRightSimplicialFrame_fibrant A (F.obj k) n)
          (fun k n => carrierRightSimplicialFrameAugmentation_quasiIso A (F.obj k) n)
      case hg =>
        exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.rightDiagramComparison_isIso K B (q.cofibrant _) a
          (q.atObject _).augmentation_weakEquivalence (R F)
          (fun k => carrierRightSimplicialFrame_cofibrant A (F.obj k))
      case hf' =>
        exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.leftDiagramComparison_isIso K B (q.cofibrant _)
          ((Diagram.forget A K).obj G) (R G) (b G)
          (fun k => CarrierDiagram.complex_isFibrant A (G.obj k).carrier)
          (fun k n => carrierRightSimplicialFrame_fibrant A (G.obj k) n)
          (fun k n => carrierRightSimplicialFrameAugmentation_quasiIso A (G.obj k) n)
      case hg' =>
        exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.rightDiagramComparison_isIso K B (q.cofibrant _) a
          (q.atObject _).augmentation_weakEquivalence (R G)
          (fun k => carrierRightSimplicialFrame_cofibrant A (G.obj k))
      · ext k n h
        change (h ≫ (f.app k).hom) ≫ ((b G).app k).app n =
          (h ≫ ((b F).app k).app n) ≫ (r.app k).app n
        have hn := congr_app ((carrierRightSimplicialFrameAugmentation A).naturality (f.app k)) n
        change (f.app k).hom ≫ ((b G).app k).app n = ((b F).app k).app n ≫ (r.app k).app n at hn
        rw [Category.assoc, hn, ← Category.assoc]
      · ext k n h
        change a.app n.unop ≫ (h ≫ (r.app k).app n) =
          (a.app n.unop ≫ h) ≫ (r.app k).app n
        exact (Category.assoc _ _ _).symm)
  exact E ≪≫ Functor.isoWhiskerRight (carrierRightSimplicialConeComparisonIso A K Y) L

/-- 概要：自然な錐比較の成分は既存の具体的な比較（Hovey §5.4）。
方針：同じ共通図式と同じ四つの比較を展開する。
規約：対象ごとの別の同型へ置き換えない。
使われ方：既存の π₀ 比較へ自然性を移す。 -/
lemma carrierSourceRightConeComparisonNatIso_app (Y : Complex A)
    {D : Type v} [Category.{w} D] (L : SSet.{u} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) (F : K ⥤ (operad A).Algebra) :
    (carrierSourceRightConeComparisonNatIso A K Y L hL).app F =
      carrierSourceRightConeComparisonIso A K Y F L hL := rfl

end SerrePositivity.EInfinity.BarrattEccles
