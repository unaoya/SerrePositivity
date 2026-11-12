module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGLastHornFinalEdge
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGOneSimplexComponentExt
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedEdges
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DataLowDimensionalPullback

/-! # 実最後外ホーンの回収閉辺と元の最後辺の一致

概要：回収された最後の閉零射の実辺は、元の指定零面の最後の辺そのもの。
方針：既知データの面への制限と二回の辺成分の比較を使い、型付き一単体外延性へ渡す。
規約：対象・端点・一次単体を厳密に保持。使われ方：回収閉辺の実 Verdier 分母性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
variable (σ : (Λ[3, 3] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)

/-- 元の実ホーンの指定零面にある最後の辺の一次単体。 -/
def dgLastHornFinalSimplex : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 1 :=
  (σ.app (Opposite.op ⦋2⦌) (horn.face 3 0 (by decide))).pullback
    (SimplexCategory.δ (0 : Fin 3)).toOrderHom

/-- 最後の実辺の始対象は回収した頂点二。 -/
lemma dgLastHornFinalSimplex_source :
    (dgLastHornFinalSimplex σ).obj 0 = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 2 :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornData.face_obj σ 0 (by decide) 1

/-- 最後の実辺の終対象は回収した頂点三。 -/
lemma dgLastHornFinalSimplex_target :
    (dgLastHornFinalSimplex σ).obj 1 = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 3 :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornData.face_obj σ 0 (by decide) 2

/-- 回収した最後の斉次成分は、元の実最後辺の唯一の成分と型付きで一致。 -/
lemma dgLastHornFinalSimplex_component :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).edgeHom 2 3 (by decide))
      ((dgLastHornFinalSimplex σ).edgeHom 0 1 (by decide)) := by
  let t := σ.app (Opposite.op ⦋2⦌) (horn.face 3 0 (by decide))
  have h₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeHom_heq_of_pullback_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ) t.toSimplexData
    (0 : Fin 4).succAboveOrderEmb.toOrderHom (0 : Fin 4).succAboveOrderEmb.injective
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData_pullback_face σ 0 (by decide)) 1 2 (by decide) (by decide)
  have h₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeHom_heq_of_pullback_eq t.toSimplexData
    (dgLastHornFinalSimplex σ).toSimplexData (SimplexCategory.δ (0 : Fin 3)).toOrderHom
    (0 : Fin 3).succAboveOrderEmb.injective rfl 0 1 (by decide) (by decide)
  exact h₀.trans h₁

/-- 回収閉零射からの実辺は、元の指定ホーンの最後の一次単体そのもの。 -/
lemma dgLastHornFinalClosed_edge :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornFinalClosed σ)).edge = dgLastHornFinalSimplex σ := by
  have hc : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornFinalClosed σ)).edge.edgeHom 0 1 (by decide) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).edgeHom 2 3 (by decide) := by
    change (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ ((_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _).symm
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornFinalCycle σ))).val = _
    exact congrArg Subtype.val ((_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _).apply_symm_apply _)
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOneSimplex_ext (dgLastHornFinalSimplex_source σ).symm
    (dgLastHornFinalSimplex_target σ).symm
      ((heq_of_eq hc).trans (dgLastHornFinalSimplex_component σ))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
