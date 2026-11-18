module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.FramedLimitComparison

/-!
# 通常の極限から右 frame の計算関手への自然変換

概要：Hovey §5.4 の計算対象への比較をすべての小図式の射に自然に束ねる。
方針：重み付き実現の係数に関する随伴の自然性と極限の射影の自然性を使う。
規約：同じ重みと関手的右 frame を使い、導来性は入力にしない。
使われ方：一般 homotopy 極限の右導来比較の自然変換。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.ComplexLimits

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.SerrePositivity.DifferentialGraded
open _root_.SerrePositivity.DiagramModel

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

attribute [local irreducible] _root_.SerrePositivity.ComplexLimits.rightFrameFamily
attribute [local implicit_reducible] _root_.SerrePositivity.ComplexLimits.rightFrameDiagram _root_.SerrePositivity.ComplexLimits.rightFrameDiagramFamily

/-- 概要：重み付き Hom は図式の係数の射に自然（Hovey §5.4）。
方針：実際の実現と Hom の随伴で対応する係数射の公式を使う。
規約：選んだ一点重みと元の図式射を固定する。
使われ方：通常の極限からの比較の図式射での自然性。 -/
lemma framedLimitHomEquiv_map {F G : K ⥤ (Complex A)} (f : F ⟶ G)
    (Y : (Complex A)) (h : Y ⟶ (_root_.SerrePositivity.ComplexLimits.framedLimitFunctor A K).obj F) :
    _root_.SerrePositivity.ComplexLimits.weightedCotensorHomEquiv A K G (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) Y
        (h ≫ (_root_.SerrePositivity.ComplexLimits.framedLimitFunctor A K).map f) =
      _root_.SerrePositivity.ComplexLimits.weightedCotensorHomEquiv A K F (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) Y h ≫
        ((FrameWeightRealization.homFamily Kᵒᵖ).map
          ((_root_.SerrePositivity.ComplexLimits.rightFrameDiagramFamily A K).map f.op).op).app (op Y) := by
  exact FrameWeightRealization.homEquiv_frame_naturality Kᵒᵖ
    ((_root_.SerrePositivity.ComplexLimits.rightFrameDiagramFamily A K).map f.op) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K) (op Y) h.op

/-- 概要：通常の極限から計算対象への比較はすべての図式射に自然（Hovey §5.4）。
方針：重み付き Hom で全単体へ移し、frame の比較と極限の射影の自然性を使う。
規約：図式の cofibrancy は要求しない。
使われ方：元の極限から計算関手への自然変換を構成する。 -/
@[reassoc]
lemma limitComparison_naturality {F G : K ⥤ (Complex A)} (f : F ⟶ G) :
    _root_.SerrePositivity.ComplexLimits.limitComparison A K F ≫ (_root_.SerrePositivity.ComplexLimits.framedLimitFunctor A K).map f =
      lim.map f ≫ _root_.SerrePositivity.ComplexLimits.limitComparison A K G := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  apply (_root_.SerrePositivity.ComplexLimits.weightedCotensorHomEquiv A K G (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) (limit F)).injective
  rw [_root_.SerrePositivity.ComplexLimits.framedLimitHomEquiv_map, _root_.SerrePositivity.ComplexLimits.weightedCotensorHomEquiv_precomp]
  have hF : _root_.SerrePositivity.ComplexLimits.weightedCotensorHomEquiv A K F (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) (limit F)
      (_root_.SerrePositivity.ComplexLimits.limitComparison A K F) =
        _root_.SerrePositivity.ComplexLimits.strictConeWeightedFamily A K F (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) (limit.cone F) :=
    (_root_.SerrePositivity.ComplexLimits.weightedCotensorHomEquiv A K F (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) (limit F)).apply_symm_apply _
  have hG : _root_.SerrePositivity.ComplexLimits.weightedCotensorHomEquiv A K G (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) (lim.obj G)
      (_root_.SerrePositivity.ComplexLimits.limitComparison A K G) =
        _root_.SerrePositivity.ComplexLimits.strictConeWeightedFamily A K G (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) (limit.cone G) :=
    (_root_.SerrePositivity.ComplexLimits.weightedCotensorHomEquiv A K G (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) (limit G)).apply_symm_apply _
  rw [hF, hG]
  apply NatTrans.ext
  funext k
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  change (((_root_.SerrePositivity.ComplexLimits.rightFrameFamily A).obj.map (f.app k.unop.unop).op).app n.unop) ≫
      ((_root_.SerrePositivity.ComplexLimits.rightFrameAugmentation A (F.obj k.unop.unop)).app n.unop ≫
        (limit.π F k.unop.unop).op) =
    ((_root_.SerrePositivity.ComplexLimits.rightFrameAugmentation A (G.obj k.unop.unop)).app n.unop ≫
      (limit.π G k.unop.unop).op) ≫ (lim.map f).op
  have hq := congr_app ((_root_.SerrePositivity.ComplexLimits.rightFrameFamily A).augmentation.naturality
    (f.app k.unop.unop).op) n.unop
  change _ ≫ (_root_.SerrePositivity.ComplexLimits.rightFrameAugmentation A (F.obj k.unop.unop)).app n.unop =
    (_root_.SerrePositivity.ComplexLimits.rightFrameAugmentation A (G.obj k.unop.unop)).app n.unop ≫ (f.app k.unop.unop).op at hq
  rw [← Category.assoc, hq, Category.assoc, Category.assoc]
  change _ ≫ (limit.π F k.unop.unop ≫ f.app k.unop.unop).op =
    _ ≫ (lim.map f ≫ limit.π G k.unop.unop).op
  exact congrArg
    (fun t => (_root_.SerrePositivity.ComplexLimits.rightFrameAugmentation A (G.obj k.unop.unop)).app n.unop ≫ t.op)
    (limMap_π f k.unop.unop).symm

/-- 概要：通常の小極限から右 frame の計算関手への実際の自然変換（Hovey §5.4）。
方針：通常の極限錐の各比較を、証明した図式射の自然性で束ねる。
規約：ホモトピー不変性・右導来普遍性は別に証明する。
使われ方：一般 homotopy 極限を右導来関手として特徴付ける比較。 -/
def limitComparisonNatTrans : (lim : (K ⥤ (Complex A)) ⥤ _) ⟶
    _root_.SerrePositivity.ComplexLimits.framedLimitFunctor A K where
  app := _root_.SerrePositivity.ComplexLimits.limitComparison A K
  naturality _ _ f := (_root_.SerrePositivity.ComplexLimits.limitComparison_naturality A K f).symm

end SerrePositivity.ComplexLimits
