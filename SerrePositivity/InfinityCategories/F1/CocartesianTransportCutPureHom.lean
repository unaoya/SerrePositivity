module

public import SerrePositivity.InfinityCategories.F1.CocartesianSourceCutMixedHom
public import SerrePositivity.InfinityCategories.F1.CocartesianMixedHomVertices

/-!
概要：元の分類作用の切断した共同評価における同時刻側の Hom を計算する。
方針：切断した豊穣恒等を混合評価し、元の輸送射への定値族を回収する。
規約：時刻零・一のどちらも、全高次の path に対する同じ作用を計算する。
使われ方：第一三角形全体と指定された strict 合成三角形の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同時刻零の全 Hom 作用は、元の始域図式の輸送射に定値。 -/
lemma cocartesianTransportHomCutSimplex_zeroHom
    {C : Type u} [Category.{u} C] (F G : CocartesianTransportDiagramCategory C) {n : ℕ}
    (σ : (nerve C) _⦋n⦌) (s : (SimplicialCategory.sHom F G) _⦋n⦌)
    (t : Fin (n + 1) →o Fin 2) (i j : Fin (n + 1)) (hij : i ≤ j)
    (hi : t i = 0) (hj : t j = 0) :
    (cocartesianTransportHomCutSimplex F G σ s t).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom
          (cocartesianTransportHomCutSimplex_obj_zero F G σ s t i hi)
          (cocartesianTransportHomCutSimplex_obj_zero F G σ s t j hj)) =
      SSet.const (SimplicialCategory.homEquiv'
        (cocartesianTransportDiagramValue F (σ.obj i))
        (cocartesianTransportDiagramValue F (σ.obj j)) (F.val.map (σ.map (homOfLE hij)))) := by
  have h := diagonalCocartesianTransportDiagramHom_normalized (strictDiagramSimplexBase σ)
    (coherentRightIntervalCutSimplex s t) ⟨ULift.up i⟩ ⟨ULift.up j⟩ hij
    (coherentRightIntervalCutSimplex_obj_zero s t i hi)
    (coherentRightIntervalCutSimplex_obj_zero s t j hj)
  rw [coherentRightIntervalCutSimplex_zeroHom s t i j hi hj, Category.assoc,
    cocartesianTransportDiagramMixedHom_identity, SSet.comp_const] at h
  exact h

/-- 同時刻一の全 Hom 作用は、元の終域図式の輸送射に定値。 -/
lemma cocartesianTransportHomCutSimplex_oneHom
    {C : Type u} [Category.{u} C] (F G : CocartesianTransportDiagramCategory C) {n : ℕ}
    (σ : (nerve C) _⦋n⦌) (s : (SimplicialCategory.sHom F G) _⦋n⦌)
    (t : Fin (n + 1) →o Fin 2) (i j : Fin (n + 1)) (hij : i ≤ j)
    (hi : t i = 1) (hj : t j = 1) :
    (cocartesianTransportHomCutSimplex F G σ s t).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom
          (cocartesianTransportHomCutSimplex_obj_one F G σ s t i hi)
          (cocartesianTransportHomCutSimplex_obj_one F G σ s t j hj)) =
      SSet.const (SimplicialCategory.homEquiv'
        (cocartesianTransportDiagramValue G (σ.obj i))
        (cocartesianTransportDiagramValue G (σ.obj j)) (G.val.map (σ.map (homOfLE hij)))) := by
  have h := diagonalCocartesianTransportDiagramHom_normalized (strictDiagramSimplexBase σ)
    (coherentRightIntervalCutSimplex s t) ⟨ULift.up i⟩ ⟨ULift.up j⟩ hij
    (coherentRightIntervalCutSimplex_obj_one s t i hi)
    (coherentRightIntervalCutSimplex_obj_one s t j hj)
  rw [coherentRightIntervalCutSimplex_oneHom s t i j hi hj, Category.assoc,
    cocartesianTransportDiagramMixedHom_identity, SSet.comp_const] at h
  exact h

end SerrePositivity.InfinityCategories
