module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.SourceRightConeComparison

/-!
# 具体的な両 frame の錐比較の終域自然性

概要：BM 命題 4.1・Hovey §5.4 の両錐比較を元の図式の関手同型へ束ねる。
方針：同じ augmentation の自然性から混合 Hom の二つの可換四角形を作る。
規約：既存の sourceRightConeComparisonIso の同じ成分を使う。
使われ方：定値図式と実際の極限計算関手の導来随伴の自然性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

namespace SerrePositivity.ComplexLimits

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomotopicalAlgebra
open _root_.SerrePositivity.DifferentialGraded
open _root_.SerrePositivity.Reedy
open _root_.SerrePositivity.DiagramModel.WeightedCones
open _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame

attribute [local implicit_reducible] CofibrantResolutionFamily.atObject

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：始域・右 frame の具体的な錐比較は終域図式に自然（Hovey §5.4）。
方針：両比較の自然な可換四角形と右錐の添字移送同型を合成する。
規約：元の複体に cofibrancy は要求せず、任意の anodyne 反転先を許す。
使われ方：π₀ の局所化 Hom 比較の後合成との両立。 -/
def sourceRightConeComparisonNatIso (Y : (Complex A))
    {D : Type v} [Category.{w} D] (L : SSet.{u} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    _root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.constantDiagramSourceHom A K (_root_.SerrePositivity.ComplexLimits.framedLimitProbe A Y) ⋙ L ≅
      _root_.SerrePositivity.ComplexLimits.framedLimitConeSpace A K Y ⋙ L := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let q := cosimplicialResolutionFamily (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A)
  let B := q.obj.obj (_root_.SerrePositivity.ComplexLimits.framedLimitProbe A Y)
  let a := q.augmentation.app (_root_.SerrePositivity.ComplexLimits.framedLimitProbe A Y)
  have := _root_.SerrePositivity.ComplexLimits.framedLimitProbe_cofibrant A Y
  let R (F : K ⥤ (Complex A)) := F ⋙ _root_.SerrePositivity.ComplexLimits.rightSimplicialFrameFamily A
  let b (F : K ⥤ (Complex A)) :=
    Functor.whiskerLeft F (_root_.SerrePositivity.ComplexLimits.rightSimplicialFrameAugmentation A)
  let e (F : K ⥤ (Complex A)) := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.mixedConeComparisonIso K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight_cofibrant K) B (q.cofibrant _)
    (q.atObject _).homotopicallyConstant a (q.atObject _).augmentation_weakEquivalence
    F (R F) (b F) (fun k => _root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.complex_isFibrant A (F.obj k))
    (fun k n => _root_.SerrePositivity.ComplexLimits.rightSimplicialFrame_fibrant A (F.obj k) n)
    (fun k n => _root_.SerrePositivity.ComplexLimits.rightSimplicialFrameAugmentation_quasiIso A (F.obj k) n)
    (fun k => _root_.SerrePositivity.ComplexLimits.rightSimplicialFrame_cofibrant A (F.obj k))
    (fun k _ _ f => _root_.SerrePositivity.ComplexLimits.rightSimplicialFrame_homotopicallyConstant A (F.obj k) f) L hL
  let E : _root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.constantDiagramSourceHom A K (_root_.SerrePositivity.ComplexLimits.framedLimitProbe A Y) ⋙ L ≅
      _root_.SerrePositivity.ComplexLimits.rightSimplicialHomFamily A K Y ⋙ coneSpace K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) ⋙ L :=
    NatIso.ofComponents e (by
      intro F G f
      let s := Functor.whiskerRight f (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom B)
      let r := Functor.whiskerRight f (_root_.SerrePositivity.ComplexLimits.rightSimplicialFrameFamily A)
      let t := Functor.whiskerRight r (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame.rightHomFunctor (_root_.SerrePositivity.ComplexLimits.framedLimitProbe A Y))
      let c := Functor.whiskerRight r (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame.mixedFunctor B)
      change L.map ((coneSpace K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)).map s) ≫ (e G).hom =
        (e F).hom ≫ L.map ((coneSpace K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)).map t)
      apply _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.kanConeComparisonIso_naturality K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)
        (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight_cofibrant K) L hL (c := c)
      case hF =>
        exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.leftDiagram_kanComplex K B (q.cofibrant _)
          (q.atObject _).homotopicallyConstant F (fun k =>
            _root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.complex_isFibrant A (F.obj k))
      case hG =>
        exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.rightDiagram_kanComplex K _ (R F)
          (fun k => _root_.SerrePositivity.ComplexLimits.rightSimplicialFrame_cofibrant A (F.obj k))
          (fun k _ _ g => _root_.SerrePositivity.ComplexLimits.rightSimplicialFrame_homotopicallyConstant A (F.obj k) g)
      case hF' =>
        exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.leftDiagram_kanComplex K B (q.cofibrant _)
          (q.atObject _).homotopicallyConstant G (fun k =>
            _root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.complex_isFibrant A (G.obj k))
      case hG' =>
        exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.rightDiagram_kanComplex K _ (R G)
          (fun k => _root_.SerrePositivity.ComplexLimits.rightSimplicialFrame_cofibrant A (G.obj k))
          (fun k _ _ g => _root_.SerrePositivity.ComplexLimits.rightSimplicialFrame_homotopicallyConstant A (G.obj k) g)
      case hf =>
        exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.leftDiagramComparison_isIso K B (q.cofibrant _) F (R F) (b F)
          (fun k => _root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.complex_isFibrant A (F.obj k)) (fun k n =>
            _root_.SerrePositivity.ComplexLimits.rightSimplicialFrame_fibrant A (F.obj k) n)
          (fun k n => _root_.SerrePositivity.ComplexLimits.rightSimplicialFrameAugmentation_quasiIso A (F.obj k) n)
      case hg =>
        exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.rightDiagramComparison_isIso K B (q.cofibrant _) a
          (q.atObject _).augmentation_weakEquivalence (R F)
          (fun k => _root_.SerrePositivity.ComplexLimits.rightSimplicialFrame_cofibrant A (F.obj k))
      case hf' =>
        exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.leftDiagramComparison_isIso K B (q.cofibrant _) G (R G) (b G)
          (fun k => _root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.complex_isFibrant A (G.obj k)) (fun k n =>
            _root_.SerrePositivity.ComplexLimits.rightSimplicialFrame_fibrant A (G.obj k) n)
          (fun k n => _root_.SerrePositivity.ComplexLimits.rightSimplicialFrameAugmentation_quasiIso A (G.obj k) n)
      case hg' =>
        exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.rightDiagramComparison_isIso K B (q.cofibrant _) a
          (q.atObject _).augmentation_weakEquivalence (R G)
          (fun k => _root_.SerrePositivity.ComplexLimits.rightSimplicialFrame_cofibrant A (G.obj k))
      · ext k n h
        change (h ≫ f.app k) ≫ ((b G).app k).app n =
          (h ≫ ((b F).app k).app n) ≫ (r.app k).app n
        have hn := congr_app ((_root_.SerrePositivity.ComplexLimits.rightSimplicialFrameAugmentation A).naturality (f.app k)) n
        change f.app k ≫ ((b G).app k).app n = ((b F).app k).app n ≫ (r.app k).app n at hn
        rw [Category.assoc, hn, ← Category.assoc]
      · ext k n h
        change a.app n.unop ≫ (h ≫ (r.app k).app n) =
          (a.app n.unop ≫ h) ≫ (r.app k).app n
        exact (Category.assoc _ _ _).symm)
  exact E ≪≫ Functor.isoWhiskerRight (_root_.SerrePositivity.ComplexLimits.rightSimplicialConeComparisonIso A K Y) L

/-- 概要：自然な錐比較の成分は既存の具体的な比較（Hovey §5.4）。
方針：同じ共通図式と同じ四つの比較を展開する。
規約：対象ごとの別の同型へ置き換えない。
使われ方：既存の π₀ 比較へ自然性を移す。 -/
lemma sourceRightConeComparisonNatIso_app (Y : (Complex A))
    {D : Type v} [Category.{w} D] (L : SSet.{u} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) (F : K ⥤ (Complex A)) :
    (_root_.SerrePositivity.ComplexLimits.sourceRightConeComparisonNatIso A K Y L hL).app F =
      _root_.SerrePositivity.ComplexLimits.sourceRightConeComparisonIso A K Y F L hL := rfl

end SerrePositivity.ComplexLimits
