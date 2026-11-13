module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.Pullback
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Square
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PushoutShape

/-! # h C の可換正方形の実現

概要：四つの指定辺の類が可換なら、その四辺を持つ実際の正方形が存在する。
方針：共通の対角の辺を選び、二つの合成三角形を対角に沿う pushout で貼る。
規約：四辺の実際の一次単体を保持する。
使われ方：S4 の TR3 の最初の二成分の実現。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 概要：下側三角形の最初の辺は正方形の下辺。
方針：有限頂点写像を計算する。規約：三角形番号一、面番号二。
使われ方：二三角形を貼った正方形の下辺。 -/
lemma stableSquareTriangle_bottomEdge :
    stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u} 1 = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> decide

/-- 概要：上側三角形の最初の辺は正方形の左辺。
方針：有限頂点写像を計算する。規約：三角形番号零、面番号二。
使われ方：二三角形を貼った正方形の左辺。 -/
lemma stableSquareTriangle_leftEdge :
    stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u} 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> decide

/-- 概要：h C で可換な四つの辺はそのまま実際の正方形の四辺になる。
方針：対角の類を辺で表し、二つの合成三角形を貼る。
規約：値域は quasicategory。使われ方：可換な射の比較のホモトピーへの持ち上げ。 -/
lemma exists_stableSquare_of_homMk_comm {X : SSet.{u}} [Quasicategory X]
    {x y x' y' : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (g : SSet.Truncated.Edge (X := (truncation 2).obj X) x' y')
    (a : SSet.Truncated.Edge (X := (truncation 2).obj X) x x')
    (b : SSet.Truncated.Edge (X := (truncation 2).obj X) y y')
    (h : SSet.Truncated.HomotopyCategory.homMk f ≫ SSet.Truncated.HomotopyCategory.homMk b =
      SSet.Truncated.HomotopyCategory.homMk a ≫ SSet.Truncated.HomotopyCategory.homMk g) :
    ∃ Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ Q = SSet.yonedaEquiv.symm f.edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ Q = SSet.yonedaEquiv.symm g.edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ Q = SSet.yonedaEquiv.symm a.edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ Q = SSet.yonedaEquiv.symm b.edge := by
  obtain ⟨k, hk⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective x y'
    (SSet.Truncated.HomotopyCategory.homMk a ≫ SSet.Truncated.HomotopyCategory.homMk g)
  obtain ⟨L⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac (h.trans hk.symm)
  obtain ⟨U⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac hk.symm
  let l : (Δ[2] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm L.simplex
  let r : (Δ[2] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm U.simplex
  have hl₂ : stdSimplex.δ (2 : Fin 3) ≫ l = SSet.yonedaEquiv.symm f.edge := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp]
    exact (congrArg (fun v ↦ X.δ 2 v) (SSet.yonedaEquiv.apply_symm_apply L.simplex)).trans
      (L.d₂.trans (SSet.yonedaEquiv.apply_symm_apply f.edge).symm)
  have hl₀ : stdSimplex.δ (0 : Fin 3) ≫ l = SSet.yonedaEquiv.symm b.edge := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp]
    exact (congrArg (fun v ↦ X.δ 0 v) (SSet.yonedaEquiv.apply_symm_apply L.simplex)).trans
      (L.d₀.trans (SSet.yonedaEquiv.apply_symm_apply b.edge).symm)
  have hr₂ : stdSimplex.δ (2 : Fin 3) ≫ r = SSet.yonedaEquiv.symm a.edge := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp]
    exact (congrArg (fun v ↦ X.δ 2 v) (SSet.yonedaEquiv.apply_symm_apply U.simplex)).trans
      (U.d₂.trans (SSet.yonedaEquiv.apply_symm_apply a.edge).symm)
  have hr₀ : stdSimplex.δ (0 : Fin 3) ≫ r = SSet.yonedaEquiv.symm g.edge := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp]
    exact (congrArg (fun v ↦ X.δ 0 v) (SSet.yonedaEquiv.apply_symm_apply U.simplex)).trans
      (U.d₀.trans (SSet.yonedaEquiv.apply_symm_apply g.edge).symm)
  have hd : stdSimplex.δ (1 : Fin 3) ≫ r = stdSimplex.δ (1 : Fin 3) ≫ l := by
    apply SSet.yonedaEquiv.injective
    simp only [stdSimplex.yonedaEquiv_δ_comp, l, r, Equiv.apply_symm_apply]
    exact U.d₁.trans L.d₁.symm
  let Q := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.desc r l hd
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · rw [← stableSquareTriangle_bottomEdge, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inr_desc]
    exact hl₂
  · rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTriangle_topEdge, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inl_desc]
    exact hr₀
  · rw [← stableSquareTriangle_leftEdge, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inl_desc]
    exact hr₂
  · rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTriangle_rightEdge, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inr_desc]
    exact hl₀

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
