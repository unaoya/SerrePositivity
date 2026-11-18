module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.RightSimplicialCones
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.Probe
public import SerrePositivity.EInfinity.BarrattEccles.CarrierConstantDiagramFrame
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Frames.MixedFrameCones

/-!
# 複体の始域 frame の錐と実際の右 frame の錐の比較

概要：BM 命題 4.1・Hovey §5.4 の両 frame 比較を具体的な小図式へ適用する。
方針：既存の試験始域の cofibrancy を証明から供給し、同じ混合 Hom の錐で比較する。
規約：元の複体の cofibrancy と単体集合モデルを入力にしない。
使われ方：定値図式からの導来 Hom と実際の homotopy 極限の計算を結ぶ。
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
open _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame

attribute [local implicit_reducible] CofibrantResolutionFamily.atObject

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：始域 frame の錐は既存の右 frame の錐と反転後に同型（Hovey §5.4）。
方針：同じ試験始域の始域 frame と右 frame の共同比較に添字移送を合成する。
規約：元の複体・図式に cofibrancy 条件はなく、試験始域は既存のものを使う。
使われ方：図式の局所化 Hom と具体的な homotopy 極限への Hom の比較。 -/
def sourceRightConeComparisonIso (Y : (Complex A)) (F : K ⥤ (Complex A))
    {D : Type v} [Category.{w} D] (L : SSet.{u} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    L.obj ((_root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.constantDiagramSourceHom A K (_root_.SerrePositivity.ComplexLimits.framedLimitProbe A Y)).obj
      F) ≅
      L.obj ((_root_.SerrePositivity.ComplexLimits.framedLimitConeSpace A K Y).obj F) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let q := cosimplicialResolutionFamily (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A)
  have := _root_.SerrePositivity.ComplexLimits.framedLimitProbe_cofibrant A Y
  let R := F ⋙ _root_.SerrePositivity.ComplexLimits.rightSimplicialFrameFamily A
  let b : F ⋙ Functor.const SimplexCategoryᵒᵖ ⟶ R :=
    Functor.whiskerLeft F (_root_.SerrePositivity.ComplexLimits.rightSimplicialFrameAugmentation A)
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.mixedConeComparisonIso K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight_cofibrant K) (q.obj.obj (_root_.SerrePositivity.ComplexLimits.framedLimitProbe A Y))
    (q.cofibrant _) (q.atObject _).homotopicallyConstant (q.augmentation.app _)
    (q.atObject _).augmentation_weakEquivalence F R b
    (fun k => _root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.complex_isFibrant A (F.obj k))
    (fun k n => _root_.SerrePositivity.ComplexLimits.rightSimplicialFrame_fibrant A (F.obj k) n)
    (fun k n => _root_.SerrePositivity.ComplexLimits.rightSimplicialFrameAugmentation_quasiIso A (F.obj k) n)
    (fun k => _root_.SerrePositivity.ComplexLimits.rightSimplicialFrame_cofibrant A (F.obj k))
    (fun k _ _ f => _root_.SerrePositivity.ComplexLimits.rightSimplicialFrame_homotopicallyConstant A (F.obj k) f) L hL ≪≫
      L.mapIso (_root_.SerrePositivity.ComplexLimits.rightSimplicialConeIso A K Y F)

end SerrePositivity.ComplexLimits
