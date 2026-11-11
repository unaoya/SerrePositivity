module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFourLastHornFinalEdge
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
variable (σ : (Λ[4, 4] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)

/-- 元の実ホーンの指定零面にある最後の辺の一次単体。 -/
def dgFourLastHornFinalSimplex : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 1 :=
  (σ.app (Opposite.op ⦋3⦌) (horn.face 4 0 (by decide))).pullback
    (SimplexCategory.δ (0 : Fin 3) ≫ SimplexCategory.δ (0 : Fin 4)).toOrderHom

/-- 最後の辺の回収は、指定零面の二つの零面と一致する。 -/
lemma dgFourLastHornFinalSimplex_eq_faces :
    dgFourLastHornFinalSimplex σ = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 0 ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 0
      (σ.app (Opposite.op ⦋3⦌) (horn.face 4 0 (by decide)))) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_comp _ (SimplexCategory.δ (0 : Fin 3)).toOrderHom
    (SimplexCategory.δ (0 : Fin 4)).toOrderHom).symm

/-- 最後の実辺の始対象は回収した頂点三。 -/
lemma dgFourLastHornFinalSimplex_source :
    (dgFourLastHornFinalSimplex σ).obj 0 = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 3 :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornData.face_obj σ 0 (by decide) 2

/-- 最後の実辺の終対象は回収した頂点四。 -/
lemma dgFourLastHornFinalSimplex_target :
    (dgFourLastHornFinalSimplex σ).obj 1 = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 4 :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornData.face_obj σ 0 (by decide) 3

/-- 回収した最後の斉次成分は、元の実最後辺の唯一の成分と型付きで一致。 -/
lemma dgFourLastHornFinalSimplex_component :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).edgeHom 3 4 (by decide))
      ((dgFourLastHornFinalSimplex σ).edgeHom 0 1 (by decide)) := by
  let t := σ.app (Opposite.op ⦋3⦌) (horn.face 4 0 (by decide))
  have h₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeHom_heq_of_pullback_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ) t.toSimplexData
    (0 : Fin 5).succAboveOrderEmb.toOrderHom (0 : Fin 5).succAboveOrderEmb.injective
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData_pullback_face σ 0 (by decide)) 2 3 (by decide) (by decide)
  have h₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeHom_heq_of_pullback_eq t.toSimplexData
    (dgFourLastHornFinalSimplex σ).toSimplexData
    (SimplexCategory.δ (0 : Fin 3) ≫ SimplexCategory.δ (0 : Fin 4)).toOrderHom
    (by decide) rfl 0 1 (by decide) (by decide)
  exact h₀.trans h₁

/-- 回収閉零射からの実辺は、元の指定ホーンの最後の一次単体そのもの。 -/
lemma dgFourLastHornFinalClosed_edge :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornFinalClosed σ)).edge = dgFourLastHornFinalSimplex σ := by
  have hc : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornFinalClosed σ)).edge.edgeHom 0 1 (by decide) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).edgeHom 3 4 (by decide) := by
    change (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ ((_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _).symm
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornFinalCycle σ))).val = _
    exact congrArg Subtype.val ((_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _).apply_symm_apply _)
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOneSimplex_ext (dgFourLastHornFinalSimplex_source σ).symm
    (dgFourLastHornFinalSimplex_target σ).symm
      ((heq_of_eq hc).trans (dgFourLastHornFinalSimplex_component σ))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
