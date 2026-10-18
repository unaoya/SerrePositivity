module
public import SerrePositivity.InfinityCategories.Stable.SquareHorizontalHomotopies

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
namespace SerrePositivity.InfinityCategories

/-- 概要：右への変形を左下で制限すると正方形の下辺になる。
方針：max(0,t)=t を各頂点で計算する。
規約：単体的な射の等号。使われ方：下辺の類との照合。 -/
lemma squareHorizontalMaxShape_source :
    ((stdSimplex.δ (1 : Fin 2) ≫ squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫
      squareHorizontalMaxShape = snd Δ[0] Δ[1] ≫ squareBottomEdge := by
  apply CartesianMonoidalCategory.hom_ext
  all_goals
    apply stdSimplex_hom_ext_vertices
    apply ConcreteCategory.hom_ext
    rintro ⟨p, q⟩
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective p
    obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective q
    fin_cases i; fin_cases j <;> rfl

/-- 概要：左からの変形は左下の頂点を固定する。
方針：min(0,t)=0 を各頂点で計算する。
規約：単体的な射の等号。使われ方：恒等成分との照合。 -/
lemma squareHorizontalMinShape_source :
    ((stdSimplex.δ (1 : Fin 2) ≫ squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫
      squareHorizontalMinShape = snd Δ[0] Δ[1] ≫
        SSet.const (squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 0 0) := by
  apply CartesianMonoidalCategory.hom_ext
  all_goals
    apply stdSimplex_hom_ext_vertices
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
    (squareDiagramHoEvaluation X 0 0).map
      (SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (squareHorizontalRightHomotopy F))) =
          squareHoBottom F := by
  have hpath : ((stdSimplex.δ (1 : Fin 2) ≫ squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫
      (squareHorizontalRightHomotopy F).h = snd Δ[0] Δ[1] ≫ (squareBottomEdge ≫ F) := by
    change _ ≫ (squareHorizontalMaxShape ≫ F) = _
    rw [← Category.assoc, squareHorizontalMaxShape_source, Category.assoc]
  have h := homotopyEvaluation_arrow_of_vertexPath (squareHorizontalRightHomotopy F)
    (stdSimplex.δ (1 : Fin 2) ≫ squareBottomEdge) (squareBottomEdge ≫ F) hpath
  have hi : SSet.yonedaEquiv
      (stdSimplex.δ (1 : Fin 2) ≫ squareBottomEdge : (Δ[0] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) =
      squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 0 0 := by
    apply Prod.ext <;> decide
  rw [hi] at h
  apply Arrow.mk_injective
  exact h.trans (SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
    (edgeOfSimplex (SSet.yonedaEquiv (squareBottomEdge ≫ F))) (squareBottomArrow F)
      (squareBottomArrow_edge F).symm)

/-- 概要：左からの水平変形は始点で恒等射を与える。
方針：左下の固定条件をホモトピーの固定成分の式へ移す。
規約：値域の quasicategory 性は不要。使われ方：比較の始点成分の合成。 -/
lemma squareHorizontalLeftHomotopy_source {X : SSet.{u}}
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    (squareDiagramHoEvaluation X 0 0).map
      (SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (squareHorizontalLeftHomotopy F))) =
          𝟙 (squareHoVertex F 0 0) := by
  have hfix : ((stdSimplex.δ (1 : Fin 2) ≫ squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫
      (squareHorizontalLeftHomotopy F).h =
        snd Δ[0] Δ[1] ≫ SSet.const (squareVertex F 0 0) := by
    change _ ≫ (squareHorizontalMinShape ≫ F) = _
    rw [← Category.assoc, squareHorizontalMinShape_source, Category.assoc, SSet.const_comp]
    rfl
  have hi : SSet.yonedaEquiv
      (stdSimplex.δ (1 : Fin 2) ≫ squareBottomEdge : (Δ[0] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) =
      squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 0 0 := by
    apply Prod.ext <;> decide
  have ha := homotopyNatTrans_fixedVertex_arrow (squareHorizontalLeftHomotopy F).h
    (stdSimplex.δ (1 : Fin 2) ≫ squareBottomEdge) (squareVertex F 0 0) hfix
  rw [hi] at ha
  apply Arrow.mk_injective
  exact (homotopyEvaluation_arrow (squareHorizontalLeftHomotopy F) _).trans ha

end SerrePositivity.InfinityCategories
