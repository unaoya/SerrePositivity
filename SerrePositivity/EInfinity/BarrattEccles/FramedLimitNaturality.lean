module

public import SerrePositivity.EInfinity.BarrattEccles.FramedLimitComparison

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

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits Opposite
open SerrePositivity.DiagramModel

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

attribute [local irreducible] rightFrameFamily
attribute [local implicit_reducible] rightFrameDiagram rightFrameDiagramFamily

/-- 概要：重み付き Hom は図式の係数の射に自然（Hovey §5.4）。
方針：実際の実現と Hom の随伴で対応する係数射の公式を使う。
規約：選んだ一点重みと元の図式射を固定する。
使われ方：通常の極限からの比較の図式射での自然性。 -/
lemma framedLimitHomEquiv_map {F G : K ⥤ (operad A).Algebra} (f : F ⟶ G)
    (Y : (operad A).Algebra) (h : Y ⟶ (framedLimitFunctor A K).obj F) :
    weightedCotensorHomEquiv A K G (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) Y
        (h ≫ (framedLimitFunctor A K).map f) =
      weightedCotensorHomEquiv A K F (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) Y h ≫
        ((FrameWeightRealization.homFamily Kᵒᵖ).map
          ((rightFrameDiagramFamily A K).map f.op).op).app (op Y) := by
  exact FrameWeightRealization.homEquiv_frame_naturality Kᵒᵖ
    ((rightFrameDiagramFamily A K).map f.op) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K) (op Y) h.op

/-- 概要：通常の極限から計算対象への比較はすべての図式射に自然（Hovey §5.4）。
方針：重み付き Hom で全単体へ移し、frame の比較と極限の射影の自然性を使う。
規約：図式の cofibrancy は要求しない。
使われ方：元の極限から計算関手への自然変換を構成する。 -/
@[reassoc]
lemma limitComparison_naturality {F G : K ⥤ (operad A).Algebra} (f : F ⟶ G) :
    limitComparison A K F ≫ (framedLimitFunctor A K).map f =
      lim.map f ≫ limitComparison A K G := by
  let := modelCategory A
  apply (weightedCotensorHomEquiv A K G (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) (limit F)).injective
  rw [framedLimitHomEquiv_map, weightedCotensorHomEquiv_precomp]
  have hF : weightedCotensorHomEquiv A K F (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) (limit F)
      (limitComparison A K F) =
        strictConeWeightedFamily A K F (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) (limit.cone F) :=
    (weightedCotensorHomEquiv A K F (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) (limit F)).apply_symm_apply _
  have hG : weightedCotensorHomEquiv A K G (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) (lim.obj G)
      (limitComparison A K G) =
        strictConeWeightedFamily A K G (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) (limit.cone G) :=
    (weightedCotensorHomEquiv A K G (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) (limit G)).apply_symm_apply _
  rw [hF, hG]
  apply NatTrans.ext
  funext k
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  change (((rightFrameFamily A).obj.map (f.app k.unop.unop).op).app n.unop) ≫
      ((rightFrameAugmentation A (F.obj k.unop.unop)).app n.unop ≫
        (limit.π F k.unop.unop).op) =
    ((rightFrameAugmentation A (G.obj k.unop.unop)).app n.unop ≫
      (limit.π G k.unop.unop).op) ≫ (lim.map f).op
  have hq := congr_app ((rightFrameFamily A).augmentation.naturality
    (f.app k.unop.unop).op) n.unop
  change _ ≫ (rightFrameAugmentation A (F.obj k.unop.unop)).app n.unop =
    (rightFrameAugmentation A (G.obj k.unop.unop)).app n.unop ≫ (f.app k.unop.unop).op at hq
  rw [← Category.assoc, hq, Category.assoc, Category.assoc]
  change _ ≫ (limit.π F k.unop.unop ≫ f.app k.unop.unop).op =
    _ ≫ (lim.map f ≫ limit.π G k.unop.unop).op
  exact congrArg
    (fun t => (rightFrameAugmentation A (G.obj k.unop.unop)).app n.unop ≫ t.op)
    (limMap_π f k.unop.unop).symm

/-- 概要：通常の小極限から右 frame の計算関手への実際の自然変換（Hovey §5.4）。
方針：通常の極限錐の各比較を、証明した図式射の自然性で束ねる。
規約：ホモトピー不変性・右導来普遍性は別に証明する。
使われ方：一般 homotopy 極限を右導来関手として特徴付ける比較。 -/
def limitComparisonNatTrans : (lim : (K ⥤ (operad A).Algebra) ⥤ _) ⟶
    framedLimitFunctor A K where
  app := limitComparison A K
  naturality _ _ f := (limitComparison_naturality A K f).symm

end SerrePositivity.EInfinity.BarrattEccles
