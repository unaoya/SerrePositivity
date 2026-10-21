module

public import SerrePositivity.InfinityCategories.F1.CocartesianSourceCutMixedHom
public import SerrePositivity.InfinityCategories.F1.CoherentPathCutRightEndpoint

/-!
概要：元の分類作用の混合 Hom を、固定成分の仮定なしに元の可変単体で表示する。
方針：右 Hom の切断座標を最後の零頂点の射へ戻し、元の共同評価へ続ける。
規約：元の source の全 Hom と全次数を保持する。
使われ方：第二三角形の可変 Hom を標準合成三角形と照合する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の右区間の混合 Hom は、元の単体を最後の零頂点で評価した族。 -/
lemma coherentRightIntervalCutSimplex_mixedHom_lastZero
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y : C} {n : ℕ}
    (s : (SimplicialCategory.sHom X Y) _⦋n⦌) (t : Fin (n + 1) →o Fin 2)
    (i j : Fin (n + 1)) (hi : t i = 0) (hj : t j = 1) :
    (coherentRightIntervalCutSimplex s t).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom
          (coherentRightIntervalCutSimplex_obj_zero s t i hi)
          (coherentRightIntervalCutSimplex_obj_one s t j hj)) =
      pathCutLastZeroMap t hi j ≫ SSet.yonedaEquiv.symm s := by
  have hm := (pathCutLastZeroMap_front t hi j).trans
    (coherentPrismCut_maximumMap t i j hi (by rw [hj]; decide))
  rw [coherentRightIntervalCutSimplex_mixedHom s t i j hi hj]
  simpa only [Category.assoc] using
    (congrArg (fun f ↦ f ≫ SSet.yonedaEquiv.symm s) hm).symm

/-- 元の分類 prism の混合 Hom は、同じ可変単体と元の共同評価の合成。 -/
lemma cocartesianTransportHomCutSimplex_mixedHom_general
    {C : Type u} [Category.{u} C] (F G : CocartesianTransportDiagramCategory C) {n : ℕ}
    (σ : (nerve C) _⦋n⦌) (s : (SimplicialCategory.sHom F G) _⦋n⦌)
    (t : Fin (n + 1) →o Fin 2) (i j : Fin (n + 1)) (hij : i ≤ j)
    (hi : t i = 0) (hj : t j = 1) :
    (cocartesianTransportHomCutSimplex F G σ s t).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom
          (cocartesianTransportHomCutSimplex_obj_zero F G σ s t i hi)
          (cocartesianTransportHomCutSimplex_obj_one F G σ s t j hj)) =
      pathCutLastZeroMap t hi j ≫ SSet.yonedaEquiv.symm s ≫
        cocartesianTransportDiagramMixedHom (σ.map (homOfLE hij)) F G := by
  have h := diagonalCocartesianTransportDiagramHom_normalized (strictDiagramSimplexBase σ)
    (coherentRightIntervalCutSimplex s t) ⟨ULift.up i⟩ ⟨ULift.up j⟩ hij
    (coherentRightIntervalCutSimplex_obj_zero s t i hi)
    (coherentRightIntervalCutSimplex_obj_one s t j hj)
  rw [coherentRightIntervalCutSimplex_mixedHom_lastZero s t i j hi hj] at h
  exact h.trans (Category.assoc _ _ _)

end SerrePositivity.InfinityCategories
