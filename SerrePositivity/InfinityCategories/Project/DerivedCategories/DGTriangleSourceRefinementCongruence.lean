module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGTriangleSourceRefinement
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedEdgeCompositionEquality

/-! # 元の実三角形と実細分辺の厳密一致に沿う始点細分の一致

概要：元の三角形と追加閉射の実辺が等しければ、細分した実三角形全体も厳密に等しい。
方針：三角形等式と実辺の始点等式を消去し、元の閉射の単射性で同じ入力へ戻す。
規約：三角 cochain 全体の一致。使われ方：同じ頂点脚の異なる図式辺からの回収の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 元の実三角形と追加閉辺の一致は、始点細分の実三角形全体の一致を与える。 -/
lemma dgSimplexSourceRefinement_congr {t t' : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 2} (ht : t = t') (q q' : D)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (t.obj 0))
    (s' : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q' ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (t'.obj 0))
    (hs : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s').edge) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexSourceRefinement t q s = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexSourceRefinement t' q' s' := by
  cases ht
  have hq : q = q' := congrArg (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 1 => a.obj 0) hs
  cases hq
  cases _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_raw_injective A D s s' hs
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
