module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNestedSecondHom
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleTwoCutCoordinates

/-!
概要：元の二射の基準二胞体を、三対象ラベルで任意の次数に表示する。
方針：既存の二重切断を零側・終側の二値ラベルに適用する。
規約：元の二射はともに可変。対象と二つの混合 Hom を同じ座標で回収する。
使われ方：全次数で長 Hom のみを置き換える構成の基準。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

lemma triangleZeroLabel_one {n : ℕ} (l : Fin (n + 1) →o Fin 3)
    {i : Fin (n + 1)} (hi : l i ≠ 0) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel l i = 1 := by
  change (if l i = 0 then (0 : Fin 2) else 1) = 1
  exact ite_eq_right hi

lemma triangleUpperLabel_one {n : ℕ} (l : Fin (n + 1) →o Fin 3)
    {i : Fin (n + 1)} (hi : l i = 2) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleUpperLabel l i = 1 := by
  change (if l i = 2 then (1 : Fin 2) else 0) = 1
  exact ite_eq_left hi

lemma triangleUpperLabel_zero_of_ne {n : ℕ} (l : Fin (n + 1) →o Fin 3)
    {i : Fin (n + 1)} (hi : l i ≠ 2) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleUpperLabel l i = 0 := by
  change (if l i = 2 then (1 : Fin 2) else 0) = 0
  exact ite_eq_right hi

lemma triangleLabel_nested {n : ℕ} (l : Fin (n + 1) →o Fin 3) :
    ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel l i = 0 → _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleUpperLabel l i = 0 := by
  intro i hi
  by_cases h : l i = 0
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleUpperLabel_zero l h
  · have hn := triangleZeroLabel_one l h
    omega

variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y Z : C} {n : ℕ}
  (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
  (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌) (l : Fin (n + 1) →o Fin 3)

/-- 元の二射の任意次数の三対象ラベル表示。 -/
def triangleLabelBaseline : (SimplicialNerve C) _⦋n⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionNestedCutSimplex σ τ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleUpperLabel l) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel l)

lemma triangleLabelBaseline_obj_zero (i : Fin (n + 1)) (hi : l i = 0) :
    (triangleLabelBaseline σ τ l).obj ⟨ULift.up i⟩ = X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionNestedCutSimplex_obj_zero σ τ _ _ (triangleLabel_nested l) i
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel_zero l hi)

lemma triangleLabelBaseline_obj_one (i : Fin (n + 1)) (hi : l i = 1) :
    (triangleLabelBaseline σ τ l).obj ⟨ULift.up i⟩ = Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionNestedCutSimplex_obj_middle σ τ _ _ i
    (triangleUpperLabel_zero_of_ne l (by omega)) (triangleZeroLabel_one l (by omega))

lemma triangleLabelBaseline_obj_two (i : Fin (n + 1)) (hi : l i = 2) :
    (triangleLabelBaseline σ τ l).obj ⟨ULift.up i⟩ = Z :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionNestedCutSimplex_obj_last σ τ _ _ i (triangleUpperLabel_one l hi)

/-- 第一短辺は元の第一射を零側の切断座標で評価したもの。 -/
lemma triangleLabelBaseline_firstHom (i j : Fin (n + 1)) (hi : l i = 0) (hj : l j = 1) :
    (triangleLabelBaseline σ τ l).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (triangleLabelBaseline_obj_zero σ τ l i hi) (triangleLabelBaseline_obj_one σ τ l j hj)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZeroMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel l) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel_zero l hi) j ≫
        SSet.yonedaEquiv.symm σ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionNestedCutSimplex_zero_middle σ τ _ _ (triangleLabel_nested l) i j
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel_zero l hi) (triangleUpperLabel_zero_of_ne l (by omega))
    (triangleZeroLabel_one l (by omega))

/-- 第二短辺も元の可変な第二射を終側の切断座標で評価したもの。 -/
lemma triangleLabelBaseline_lastHom (i j : Fin (n + 1)) (hi : l i = 1) (hj : l j = 2) :
    (triangleLabelBaseline σ τ l).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (triangleLabelBaseline_obj_one σ τ l i hi) (triangleLabelBaseline_obj_two σ τ l j hj)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZeroMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleUpperLabel l) (triangleUpperLabel_zero_of_ne l (by omega)) j ≫
        SSet.yonedaEquiv.symm τ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleNestedSecondHom σ τ _ _ i j
    (triangleUpperLabel_zero_of_ne l (by omega)) (triangleZeroLabel_one l (by omega))
    (triangleUpperLabel_one l hj)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
