module

public import SerrePositivity.EInfinity.BarrattEccles.CarrierRightSimplicialCones
public import SerrePositivity.EInfinity.BarrattEccles.CarrierConstantDiagramFrame
public import SerrePositivity.EInfinity.BarrattEccles.CarrierDiagramForget
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Frames.MixedFrameCones

/-!
# 底の始域 frame の錐と元の右 frame の底の錐の比較

概要：BM 命題 4.1・Hovey §5.4 の混合 Hom 比較を底の具体的な両 frame へ適用する。
方針：同じ複体の試験始域と元の右 frame の底を共通の混合 Hom で結ぶ。
規約：元の複体・図式に cofibrancy は要求せず、単体集合モデルも仮定しない。
使われ方：底の定値図式からの局所化 Hom と実際の計算対象の底への Hom の比較。
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
open _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame

attribute [local implicit_reducible] CofibrantResolutionFamily.atObject

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：底の両 frame の錐は anodyne 反転後に同型（Hovey §5.4）。
方針：同じ複体の試験始域と右 frame の底へ混合 Hom 比較を代入する。
規約：元の試験始域・図式・重み・右 frame を保持する。
使われ方：底の両局所化 Hom を同じ錐の π₀ で比較する。 -/
def carrierSourceRightConeComparisonIso (Y : Complex A) (F : K ⥤ (operad A).Algebra)
    {D : Type v} [Category.{w} D] (L : SSet.{u} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    L.obj ((CarrierDiagram.constantDiagramSourceHom A K (carrierFramedLimitProbe A Y)).obj
      ((Diagram.forget A K).obj F)) ≅ L.obj ((carrierFramedLimitConeSpace A K Y).obj F) := by
  let := projectiveModelCategory A
  let q := cosimplicialResolutionFamily (carrierProbeFactorization A)
  have := carrierFramedLimitProbe_cofibrant A Y
  let R := F ⋙ carrierRightSimplicialFrameFamily A
  let b := Functor.whiskerLeft F (carrierRightSimplicialFrameAugmentation A)
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.mixedConeComparisonIso K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight_cofibrant K) (q.obj.obj (carrierFramedLimitProbe A Y))
    (q.cofibrant _) (q.atObject _).homotopicallyConstant (q.augmentation.app _)
    (q.atObject _).augmentation_weakEquivalence ((Diagram.forget A K).obj F) R b
    (fun k => CarrierDiagram.complex_isFibrant A (F.obj k).carrier)
    (fun k n => carrierRightSimplicialFrame_fibrant A (F.obj k) n)
    (fun k n => carrierRightSimplicialFrameAugmentation_quasiIso A (F.obj k) n)
    (fun k => carrierRightSimplicialFrame_cofibrant A (F.obj k))
    (fun k _ _ f => carrierRightSimplicialFrame_homotopicallyConstant A (F.obj k) f) L hL ≪≫
      L.mapIso (carrierRightSimplicialConeIso A K Y F)

end SerrePositivity.EInfinity.BarrattEccles
