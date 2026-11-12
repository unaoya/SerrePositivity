module
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.HomotopyNatTrans
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.Pullback
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.SimplexVertexDetection
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CommutativeSquareRealization
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HomotopyEvaluationClass
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HomotopyEvaluationPath
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PushoutShape

/-! # 可換正方形から辺のホモトピーへ

概要：可換な四辺から二辺のホモトピーを作り、両端の道を厳密に保持する。
方針：実現した正方形を区間のホモトピーと読み、縦の二辺を評価する。
規約：ホモトピーのパラメーターは第二座標。
使われ方：S4 の TR3 の span の比較。

対応節は Kerodon 1.4（Tag 0039）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories

/-- 概要：区間の端点を含めた円柱は正方形の縦の辺を表す。
方針：有限頂点で二座標を計算する。
規約：零端点が左辺、一端点が右辺。使われ方：ホモトピーの端点の道。 -/
lemma stableArrowEndpointCylinder (i : Fin 2) :
    (stdSimplex.δ i ▷ (Δ[1] : SSet.{u})) = snd Δ[0] Δ[1] ≫
      (if i = 1 then _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge else _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge) := by
  fin_cases i
  all_goals
    apply CartesianMonoidalCategory.hom_ext
    all_goals
      apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
      apply ConcreteCategory.hom_ext
      rintro ⟨p, q⟩
      obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective p
      obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective q
      fin_cases i; fin_cases j <;> rfl

/-- 概要：可換な辺の類から両端の道を指定した実際のホモトピーを得る。
方針：実現した正方形をホモトピーと読み、縦の二辺を端点の制限として記録する。
規約：四つの入力辺の一次単体を厳密に保持する。使われ方：TR3 の最初の二成分。 -/
lemma exists_arrowHomotopy_of_homMk_comm {X : SSet.{u}} [Quasicategory X]
    {x y x' y' : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (g : SSet.Truncated.Edge (X := (truncation 2).obj X) x' y')
    (a : SSet.Truncated.Edge (X := (truncation 2).obj X) x x')
    (b : SSet.Truncated.Edge (X := (truncation 2).obj X) y y')
    (h : SSet.Truncated.HomotopyCategory.homMk f ≫ SSet.Truncated.HomotopyCategory.homMk b =
      SSet.Truncated.HomotopyCategory.homMk a ≫ SSet.Truncated.HomotopyCategory.homMk g) :
    ∃ H : SSet.Homotopy (SSet.yonedaEquiv.symm f.edge) (SSet.yonedaEquiv.symm g.edge),
      (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
        snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm a.edge ∧
      (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
        snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm b.edge := by
  obtain ⟨Q, h₀, h₁, hl, hr⟩ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.exists_stableSquare_of_homMk_comm f g a b h
  let H : SSet.Homotopy (SSet.yonedaEquiv.symm f.edge) (SSet.yonedaEquiv.symm g.edge) := {
    h := Q
    h₀ := by change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ Q = _; exact h₀
    h₁ := by change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ Q = _; exact h₁
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro z
      exact False.elim z.1.property }
  refine ⟨H, ?_, ?_⟩
  · change _ ≫ Q = _
    rw [stableArrowEndpointCylinder]
    change (snd (Δ[0] : SSet.{u}) Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge) ≫ Q = _
    rw [Category.assoc, hl]
    rfl
  · change _ ≫ Q = _
    rw [stableArrowEndpointCylinder]
    change (snd (Δ[0] : SSet.{u}) Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge) ≫ Q = _
    rw [Category.assoc, hr]
    rfl

/-- 概要：頂点で指定した道を持つホモトピーの自然変換の成分はその道の類である。
方針：評価した関手辺を道の辺と照合し、両端を指定した自然変換の成分へ戻す。
規約：端点の輸送は Arrow の等式に含める。使われ方：TR3 の指定成分の検査。 -/
lemma homotopyNatTransOfEndpoints_vertexPath_arrow {A X : SSet.{u}} {F G : A ⟶ X}
    (H : SSet.Homotopy F G) (i : (Δ[0] : SSet.{u}) ⟶ A) {x y : X _⦋0⦌}
    (a : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (h : (i ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm a.edge) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyNatTransOfEndpoints H.h H.h₀ H.h₁).app
      (SSet.HomotopyCategory.mk (SSet.yonedaEquiv i))) =
        Arrow.mk (SSet.Truncated.HomotopyCategory.homMk a) := by
  have he := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyEvaluation_arrow_of_vertexPath H i (SSet.yonedaEquiv.symm a.edge) h
  have ha := SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv (SSet.yonedaEquiv.symm a.edge))) a
      (SSet.yonedaEquiv.apply_symm_apply a.edge)
  exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyEvaluationOfEndpoints_arrow H (SSet.yonedaEquiv i)).symm.trans (he.trans ha)

end SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories
