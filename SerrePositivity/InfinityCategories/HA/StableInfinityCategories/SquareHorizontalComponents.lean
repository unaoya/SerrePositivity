module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SquareHorizontalHomotopies

/-! # 水平変形の始点成分

概要：右への変形の始点成分は下辺、左からの変形の始点成分は恒等射である。
方針：左下の頂点上の道を計算し、ホモトピーの評価の式を適用する。
規約：四角形の始点の表示による輸送を含める。
使われ方：S4 の接続射の後の零合成の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：右への変形を左下で制限すると正方形の下辺になる。
方針：max(0,t)=t を各頂点で計算する。
規約：単体的な射の等号。使われ方：下辺の類との照合。 -/
lemma squareHorizontalMaxShape_source :
    ((stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareHorizontalMaxShape = snd Δ[0] Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge := by
  apply CartesianMonoidalCategory.hom_ext
  all_goals
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
    apply ConcreteCategory.hom_ext
    rintro ⟨p, q⟩
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective p
    obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective q
    fin_cases i; fin_cases j <;> rfl

/-- 概要：左からの変形は左下の頂点を固定する。
方針：min(0,t)=0 を各頂点で計算する。
規約：単体的な射の等号。使われ方：恒等成分との照合。 -/
lemma squareHorizontalMinShape_source :
    ((stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareHorizontalMinShape = snd Δ[0] Δ[1] ≫
        SSet.const (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 0 0) := by
  apply CartesianMonoidalCategory.hom_ext
  all_goals
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
    apply ConcreteCategory.hom_ext
    rintro ⟨p, q⟩
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective p
    obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective q
    fin_cases i; fin_cases j <;> rfl

/-- 概要：右への水平変形の始点成分は元の四角形の下辺の類である。
方針：左下での道の式とホモトピーの評価の式を適用する。
規約：値域の quasicategory 性は不要。使われ方：零合成の比較の始点。 -/
lemma squareHorizontalRightHomotopy_source {X : SSet.{u}}
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).map
      (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareHorizontalRightHomotopy F))) =
          _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoBottom F := by
  have hpath : ((stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareHorizontalRightHomotopy F).h = snd Δ[0] Δ[1] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ F) := by
    change _ ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareHorizontalMaxShape ≫ F) = _
    rw [← Category.assoc, squareHorizontalMaxShape_source, Category.assoc]
  have h := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyEvaluation_arrow_of_vertexPath (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareHorizontalRightHomotopy F)
    (stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ F) hpath
  have hi : SSet.yonedaEquiv
      (stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge : (Δ[0] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 0 0 := by
    apply Prod.ext <;> decide
  rw [hi] at h
  apply Arrow.mk_injective
  exact h.trans (SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ F))) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow F)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow_edge F).symm)

/-- 概要：左からの水平変形は始点で恒等射を与える。
方針：左下の固定条件をホモトピーの固定成分の式へ移す。
規約：値域の quasicategory 性は不要。使われ方：比較の始点成分の合成。 -/
lemma squareHorizontalLeftHomotopy_source {X : SSet.{u}}
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).map
      (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareHorizontalLeftHomotopy F))) =
          𝟙 (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex F 0 0) := by
  have hfix : ((stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareHorizontalLeftHomotopy F).h =
        snd Δ[0] Δ[1] ≫ SSet.const (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex F 0 0) := by
    change _ ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareHorizontalMinShape ≫ F) = _
    rw [← Category.assoc, squareHorizontalMinShape_source, Category.assoc, SSet.const_comp]
    rfl
  have hi : SSet.yonedaEquiv
      (stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge : (Δ[0] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 0 0 := by
    apply Prod.ext <;> decide
  have ha := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyNatTrans_fixedVertex_arrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareHorizontalLeftHomotopy F).h
    (stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex F 0 0) hfix
  rw [hi] at ha
  apply Arrow.mk_injective
  exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyEvaluation_arrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareHorizontalLeftHomotopy F) _).trans ha

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
