module

public import SerrePositivity.KST.LocalizingInvariants.HomotopyFiberSquareComparison
public import SerrePositivity.KST.LocalizingInvariants.FunctorHomArrowTransport

/-!
概要：BF fiber 正方形の全比較の右辺制限を、元の cospan の第一枝の制限へ戻す。
方針：正方形の形状同型で右辺を図式側の包含に同定し、h Fun の前合成へ移す。
規約：頂点だけでなく辺全体の比較。使われ方：輸送単位を含む模型 cube の右辺計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants


namespace HomotopyFiberConeComparison

def rightShape : (Δ[1] : SSet.{u + 1}) ⟶
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve (AsSmall.{u} Limits.WalkingCospan)) :=
  horn₂₂.ι₀₂ ≫ CospanShape.strictCospanHornIso.{u, u + 1}.inv

lemma squareShape_right : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ squareShape.{u} =
    rightShape ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] _ := by
  rw [squareShape, ← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_rightEdge, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, ← Category.assoc]
  rfl

lemma square_right_restriction {F G : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u + 1})
    ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (AsSmall.{u} Limits.WalkingCospan))) ⟶ Sp.{u}}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G) :
    Arrow.mk (homPre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge (homPre squareShape α)) =
      Arrow.mk (homPre rightShape (homPre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] _) α)) := by
  rw [← homPre_comp, ← homPre_comp]
  exact congrArg (fun k ↦ Arrow.mk (homPre k α)) squareShape_right

variable {X Y X' Y' : OmegaSpectrum.{u}} (p : X ⟶ Y) (q : X' ⟶ Y')
  (a : X ⟶ X') (b : Y ⟶ Y') (h : p ≫ b = a ≫ q)

lemma squareHom_right : Arrow.mk (homPre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge (squareHom p q a b h)) =
    Arrow.mk (homPre rightShape (homPre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] _) (cubeHom p q a b h))) :=
  square_right_restriction _

end HomotopyFiberConeComparison
end SerrePositivity.KST.LocalizingInvariants
