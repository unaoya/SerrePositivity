module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFourSimplexTopEquation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FixedHomReplacement

/-! # 四次単体の欠面 Q の置換と最上位 rhs

概要：欠面成分を Q で置換しても既知部分 K と最後辺は変わらず、最上位 rhs は K+f34 Q。
方針：固定成分の置換の自己評価と他成分の保存を、実右辺の分解へ渡す。
規約：次数 −2 の Q と次数 −3 の最上位未知。使われ方：実四次ホーンの二未知微分式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
variable (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D 4) (Q : _root_.SerrePositivity.DifferentialGraded.GradedHom A (s.obj 0) (s.obj 3) (-2))

/-- 四次単体の欠面最上位成分だけを、型付きの Q で置き換える。 -/
def dgFourSimplexWithQ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D 4 :=
  s.replaceFixed {0, 1, 2, 3} 0 3 (-2) (by decide) (by decide) (by decide) (by decide) Q

/-- 欠面成分は挿入した Q そのもの。 -/
lemma dgFourSimplexWithQ_component :
    (dgFourSimplexWithQ s Q).hom {0, 1, 2, 3} 0 3 (-2)
      (by decide) (by decide) (by decide) (by decide) = Q :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed_hom_same _ _ _ _ _ _ _ _ _ _

/-- Q の置換は最後の辺を厳密に保つ。 -/
lemma dgFourSimplexWithQ_lastEdge :
    (dgFourSimplexWithQ s Q).edgeHom 3 4 (by decide) = s.edgeHom 3 4 (by decide) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed_hom_of_ne _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by decide)

/-- Q の置換は最上位 rhs の既知部分を厳密に保つ。 -/
lemma dgFourSimplexWithQ_topResidual :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourSimplexTopResidual (dgFourSimplexWithQ s Q) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourSimplexTopResidual s := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourSimplexTopResidual, dgFourSimplexWithQ,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.edgeHom, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.tripleHom]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed_hom_of_ne _ _ _ _ _ _ _ _ _ _
    {0, 2, 3, 4} 0 4 (-2) (by decide) (by decide) (by decide) (by decide) (by decide)]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed_hom_of_ne _ _ _ _ _ _ _ _ _ _
    {1, 2, 3, 4} 1 4 (-2) (by decide) (by decide) (by decide) (by decide) (by decide)]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed_hom_of_ne _ _ _ _ _ _ _ _ _ _
    {0, 1} 0 1 0 (by decide) (by decide) (by decide) (by decide) (by decide)]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed_hom_of_ne _ _ _ _ _ _ _ _ _ _
    {0, 1, 3, 4} 0 4 (-2) (by decide) (by decide) (by decide) (by decide) (by decide)]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed_hom_of_ne _ _ _ _ _ _ _ _ _ _
    {2, 3, 4} 2 4 (-1) (by decide) (by decide) (by decide) (by decide) (by decide)]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed_hom_of_ne _ _ _ _ _ _ _ _ _ _
    {0, 1, 2} 0 2 (-1) (by decide) (by decide) (by decide) (by decide) (by decide)]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed_hom_of_ne _ _ _ _ _ _ _ _ _ _
    {0, 1, 2, 4} 0 4 (-2) (by decide) (by decide) (by decide) (by decide) (by decide)]

/-- Q を挿入した実最上位 rhs は、既知残差と最後辺による Q の後合成の和。 -/
lemma dgFourSimplexWithQ_rhs_top :
    (dgFourSimplexWithQ s Q).rhs Finset.univ 0 4 (-3)
      (by decide) (by decide) (by decide) (by decide) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourSimplexTopResidual s + _root_.SerrePositivity.DifferentialGraded.compose A (s.edgeHom 3 4 (by decide)) Q (by decide) := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourSimplex_rhs_top (dgFourSimplexWithQ s Q)).trans
    (congrArg₂ (fun (f g : _root_.SerrePositivity.DifferentialGraded.GradedHom A (s.obj 0) (s.obj 4) (-2)) => f + g)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourSimplexWithQ_topResidual s Q)
      (congrArg₂ (fun (f : _root_.SerrePositivity.DifferentialGraded.GradedHom A (s.obj 3) (s.obj 4) 0)
        (g : _root_.SerrePositivity.DifferentialGraded.GradedHom A (s.obj 0) (s.obj 3) (-2)) => _root_.SerrePositivity.DifferentialGraded.compose A f g (by decide))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourSimplexWithQ_lastEdge s Q) (dgFourSimplexWithQ_component s Q)))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
