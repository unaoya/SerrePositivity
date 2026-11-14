module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PastingOuterToRightHomotopy
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberRotationConnecting
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SquareHorizontalComponents
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionTransposeComparison

/-! # 回転接続射を比較する四角形の射

概要：一回目の長方形の外側から右面へ進み、二回目の比較を転置して合成する。
方針：四角形の関手圏のホモトピー圏で合成し、対角の成分を計算する。
規約：三角構造は仮定しない。使われ方：回転列の第三接続射と懸垂の射の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：外側から右面への変形を四角形の関手圏の h の射として表す。
方針：変形を表す関手辺の類を取る。
規約：普遍性の仮定は不要。使われ方：二回の回転の比較の第一因子。 -/
def pastingOuterToRightHom {X : SSet.{u}}
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1)) :
      hoFunctor.obj ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)) ⟶
        SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 0)) :=
  SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterToRightHomotopy F))

/-- 概要：外側から右面への比較の始点成分は左面の下辺。
方針：始点上の道を下辺の単体と照合する。
規約：端点の表示を Arrow の等号に含める。使われ方：懸垂の始点の射の判定。 -/
lemma pastingOuterToRightHom_source_arrow {X : SSet.{u}}
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).map (pastingOuterToRightHom F)) =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoBottom (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyEvaluation_arrow_of_vertexPath (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterToRightHomotopy F)
    (stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterToRightHomotopy_source F)
  have hi : SSet.yonedaEquiv
      (stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge : (Δ[0] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 0 0 := by
    apply Prod.ext <;> decide
  rw [hi] at h
  exact h.trans (SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2)))
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2)) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow_edge _).symm)

/-- 概要：外側から右面への比較の終点成分は恒等射。
方針：右上の固定条件をホモトピー成分の式へ移す。
規約：同じ右上の頂点を評価する。使われ方：比較の終点成分の合成。 -/
lemma pastingOuterToRightHom_target {X : SSet.{u}}
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 1 1).map (pastingOuterToRightHom F) =
      𝟙 (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1) 1 1) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyNatTrans_fixedVertex_arrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterToRightHomotopy F).h
    (stdSimplex.δ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1) 1 1) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterToRightHomotopy_target F)
  have hi : SSet.yonedaEquiv
      (stdSimplex.δ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge : (Δ[0] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 1 1 := by
    apply Prod.ext <;> decide
  rw [hi] at h
  apply Arrow.mk_injective
  exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyEvaluation_arrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterToRightHomotopy F) _).trans h

/-- 概要：始点固定の回転比較を始点で評価すると端点の等号輸送になる。
方針：固定頂点の成分を恒等射と Arrow として比較する。
規約：安定性と零射は不要。使われ方：二回の比較の始点成分の合成。 -/
lemma CofiberRotationRectangle.comparisonHomotopy_source_map {X : SSet.{u}}
    {t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X} (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberRotationRectangle t) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).map
      (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy r.comparisonHomotopy)) =
      eqToHom (congrArg SSet.HomotopyCategory.mk r.suspensionSquare.source_eq.symm) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyNatTrans_fixedVertex_arrow r.comparisonHomotopy.h
    (stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 0 0) r.comparisonHomotopy_source
  have hi : SSet.yonedaEquiv
      (stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge : (Δ[0] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 0 0 := by
    apply Prod.ext <;> decide
  rw [hi] at h
  have he := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyEvaluation_arrow r.comparisonHomotopy _).trans h
  obtain ⟨hX, hY, hf⟩ := (Arrow.mk_eq_mk_iff _ _).mp he
  exact hf.trans (by simp only [Category.id_comp, eqToHom_trans])

/-- 概要：二回の回転から最初の懸垂と転置した次の懸垂の間の射を得る。
方針：外側から右面への比較に、二回目の始点固定比較の転置を合成する。
規約：二つの回転長方形を指定する。使われ方：第三接続射の符号の比較。 -/
def CofiberRotationRectangle.suspensionComparison {X : SSet.{u}} [Quasicategory X]
    {t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X} (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberRotationRectangle t)
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberRotationRectangle r.rotatedZeroTriangle) :
    (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex r.suspensionSquare.square) :
      hoFunctor.obj ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)) ⟶
        SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex q.suspensionSquare.transpose.square) :=
  pastingOuterToRightHom r.diagram ≫
    (hoFunctor.map ((pre (β_ (Δ[1] : SSet.{u}) Δ[1]).hom).app X)).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy q.comparisonHomotopy))

/-- 概要：二回の回転の比較の終点成分は回転後の列の接続射。
方針：第一因子の恒等成分を消し、転置で保たれる第二因子の成分を接続射と照合する。
規約：指定した次の懸垂に値を取る。使われ方：懸垂の関手作用との比較。 -/
lemma CofiberRotationRectangle.suspensionComparison_target {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms (hoFunctor.obj X)] {t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X}
    (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberRotationRectangle t) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberRotationRectangle r.rotatedZeroTriangle) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 1 1).map (r.suspensionComparison q) =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension r.rotatedZeroTriangle r.rotated_isCofiber
        q.suspensionSquare := by
  dsimp only [suspensionComparison]
  erw [Functor.map_comp, pastingOuterToRightHom_target, Category.id_comp,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation_transpose]
  apply Arrow.mk_injective
  exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyEvaluationOfEndpoints_arrow q.comparisonHomotopy _).trans
    (congrArg Arrow.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberComparison_τ₃_eq_connectingToSuspension
      r.rotatedZeroTriangle r.rotated_isCofiber q.suspensionSquare
      q.comparisonHomotopy q.comparisonHomotopy_source))

/-- 概要：二回の回転の比較の始点成分は元の第一射を端点の等号で輸送した射。
方針：第一因子の下辺と第二因子の恒等成分を合成する。
規約：二つの懸垂の指定始点へ輸送する。使われ方：懸垂の関手作用との照合。 -/
lemma CofiberRotationRectangle.suspensionComparison_source {X : SSet.{u}} [Quasicategory X]
    {t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X} (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberRotationRectangle t)
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberRotationRectangle r.rotatedZeroTriangle) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).map (r.suspensionComparison q) =
      eqToHom (congrArg SSet.HomotopyCategory.mk r.suspensionSquare.source_eq) ≫
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoBottom t.square ≫ eqToHom (congrArg SSet.HomotopyCategory.mk
          (r.rotated_source.symm.trans q.suspensionSquare.source_eq.symm)) := by
  have ha := pastingOuterToRightHom_source_arrow r.diagram
  rw [r.left_eq] at ha
  obtain ⟨hX, hY, hf⟩ := (Arrow.mk_eq_mk_iff _ _).mp ha
  dsimp only [suspensionComparison]
  erw [Functor.map_comp, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation_transpose,
    q.comparisonHomotopy_source_map, hf]
  simp only [Category.assoc, eqToHom_trans]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
