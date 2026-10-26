module

public import SerrePositivity.InfinityCategories.F1.Diagrams.TriangleLabelBaseline

/-!
概要：三対象ラベルの基準二胞体の、同じ対象内の全 Hom を照合する。
方針：既存の二重切断の純粋 Hom の公式を同じ対象へ正規化する。
規約：元の二短辺の単体はともに可変。
使われ方：全次数の長 Hom 置換の両側の単位則。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y Z : C} {n : ℕ}
  (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
  (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌) (l : Fin (n + 1) →o Fin 3)

lemma triangleLabelBaseline_zeroHom (i j : Fin (n + 1)) (hi : l i = 0) (hj : l j = 0) :
    (triangleLabelBaseline σ τ l).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (triangleLabelBaseline_obj_zero σ τ l i hi) (triangleLabelBaseline_obj_zero σ τ l j hj)) =
      CartesianMonoidalCategory.toUnit _ ≫ eId SSet X :=
  coherentCompositionNestedCutSimplex_zeroHom σ τ _ _ (triangleLabel_nested l) i j
    (triangleZeroLabel_zero l hi) (triangleZeroLabel_zero l hj)

lemma triangleLabelBaseline_oneHom (i j : Fin (n + 1)) (hi : l i = 1) (hj : l j = 1) :
    (triangleLabelBaseline σ τ l).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (triangleLabelBaseline_obj_one σ τ l i hi) (triangleLabelBaseline_obj_one σ τ l j hj)) =
      CartesianMonoidalCategory.toUnit _ ≫ eId SSet Y :=
  coherentCompositionNestedCutSimplex_middleHom σ τ _ _ i j
    (triangleUpperLabel_zero_of_ne l (by omega)) (triangleUpperLabel_zero_of_ne l (by omega))
    (triangleZeroLabel_one l (by omega)) (triangleZeroLabel_one l (by omega))

lemma triangleLabelBaseline_twoHom (i j : Fin (n + 1)) (hi : l i = 2) (hj : l j = 2) :
    (triangleLabelBaseline σ τ l).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (triangleLabelBaseline_obj_two σ τ l i hi) (triangleLabelBaseline_obj_two σ τ l j hj)) =
      CartesianMonoidalCategory.toUnit _ ≫ eId SSet Z :=
  coherentCompositionNestedCutSimplex_lastHom σ τ _ _ i j
    (triangleUpperLabel_one l hi) (triangleUpperLabel_one l hj)

end SerrePositivity.InfinityCategories
