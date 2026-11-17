module

public import SerrePositivity.EInfinity.BarrattEccles.CarrierFramedLimitStrictFamilies
public import SerrePositivity.EInfinity.BarrattEccles.CarrierSourceRightConeComparison
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.KanConeClasses

/-!
# 両 frame の比較は元の通常の錐の同じ類を結ぶ

概要：BM 命題 4.1・Hovey §5.4 の具体的な両錐比較が元の錐の類を保つ。
方針：同じ混合 Hom 内での厳密な族の一致を Kan 錐比較のクラス計算へ移す。
規約：始域側は既存の CarrierDiagram.constantDiagramSourceClass、右側は元の通常の錐の族。
使われ方：coneToFramedLimit と導来 Hom 同値の正規化。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits _root_.HomotopicalAlgebra
open SerrePositivity.DifferentialGraded
open SerrePositivity.Reedy
open _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame

attribute [local implicit_reducible] CofibrantResolutionFamily.atObject

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：両 frame の錐比較は元の通常の錐の同じ類を結ぶ（Hovey §5.4）。
方針：始域側の類を実際の随伴族で表示し、混合 Hom の族の一致を使う。
規約：元の錐と同じ試験始域の比較を使う。
使われ方：右錐の添字移送に関する零単体計算へ接続する。 -/
lemma carrierSourceRightConeComparisonIso_strictClass (F : K ⥤ (operad A).Algebra) (c : Cone
  ((Diagram.forget A K).obj F)) :
    let f : (Functor.const K).obj (carrierFramedLimitProbe A c.pt) ⟶ (Diagram.forget A K).obj F :=
      (Functor.const K).map ((carrierFramedLimitProbeComparison A).app c.pt) ≫ c.π
    (carrierSourceRightConeComparisonIso A K c.pt F SSet.π₀Functor
        SimplicialModel.PiZeroLocalization.inverts_anodyne).hom
      (CarrierDiagram.constantDiagramSourceClass A K f) =
      SSet.mapπ₀ (carrierRightSimplicialConeIso A K c.pt F).hom
        (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneClass K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)
          (carrierStrictSimplicialConeFamily A K F c)) := by
  let := projectiveModelCategory A
  let q := cosimplicialResolutionFamily (carrierProbeFactorization A)
  let P := carrierFramedLimitProbe A c.pt
  have := carrierFramedLimitProbe_cofibrant A c.pt
  let f : (Functor.const K).obj P ⟶ (Diagram.forget A K).obj F :=
    (Functor.const K).map ((carrierFramedLimitProbeComparison A).app c.pt) ≫ c.π
  let B := q.obj.obj P
  let R := F ⋙ carrierRightSimplicialFrameFamily A
  let b := Functor.whiskerLeft F (carrierRightSimplicialFrameAugmentation A)
  let l := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.leftDiagramComparison K B ((Diagram.forget A K).obj F) R b
  let r := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.rightDiagramComparison K B (q.augmentation.app P) R
  let s := (CarrierDiagram.constantDiagramHomEquiv A K P ((Diagram.forget A K).obj F))
    ((CarrierDiagram.constantDiagramComparison A K).app P ≫ f)
  let t := carrierStrictSimplicialConeFamily A K F c
  have hs := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.kanConeComparisonIso_class K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight_cofibrant K) l r
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.leftDiagram_kanComplex K B (q.cofibrant P) (q.atObject P).homotopicallyConstant
      ((Diagram.forget A K).obj F)
      (fun k => CarrierDiagram.complex_isFibrant A (F.obj k).carrier))
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.rightDiagram_kanComplex K P R (fun k => carrierRightSimplicialFrame_cofibrant A (F.obj k))
      (fun k _ _ g => carrierRightSimplicialFrame_homotopicallyConstant A (F.obj k) g))
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.leftDiagramComparison_isIso K B (q.cofibrant P) ((Diagram.forget A K).obj F) R b (fun k =>
      CarrierDiagram.complex_isFibrant A (F.obj k).carrier)
      (fun k n => carrierRightSimplicialFrame_fibrant A (F.obj k) n)
      (fun k n => carrierRightSimplicialFrameAugmentation_quasiIso A (F.obj k) n))
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.rightDiagramComparison_isIso K B (q.cofibrant P) (q.augmentation.app P)
      (q.atObject P).augmentation_weakEquivalence R
      (fun k => carrierRightSimplicialFrame_cofibrant A (F.obj k))) s t
        (carrierStrictConeFamilies_mixed A K F c)
  dsimp only
  rw [CarrierDiagram.constantDiagramSourceClass_eq_coneClass]
  exact congrArg (SSet.mapπ₀ (carrierRightSimplicialConeIso A K c.pt F).hom) hs

end SerrePositivity.EInfinity.BarrattEccles
