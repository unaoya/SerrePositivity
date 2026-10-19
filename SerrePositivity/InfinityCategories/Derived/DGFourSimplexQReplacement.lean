module
public import SerrePositivity.InfinityCategories.Derived.DGFourSimplexTopEquation
public import SerrePositivity.InfinityCategories.DGNerve.FixedHomReplacement

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
namespace SerrePositivity.InfinityCategories
open DifferentialGraded DGNerve
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]
variable (s : SimplexData A D 4) (Q : GradedHom A (s.obj 0) (s.obj 3) (-2))

/-- 四次単体の欠面最上位成分だけを、型付きの Q で置き換える。 -/
def dgFourSimplexWithQ : SimplexData A D 4 :=
  s.replaceFixed {0, 1, 2, 3} 0 3 (-2) (by decide) (by decide) (by decide) (by decide) Q

/-- 欠面成分は挿入した Q そのもの。 -/
lemma dgFourSimplexWithQ_component :
    (dgFourSimplexWithQ s Q).hom {0, 1, 2, 3} 0 3 (-2)
      (by decide) (by decide) (by decide) (by decide) = Q :=
  SimplexData.replaceFixed_hom_same _ _ _ _ _ _ _ _ _ _

/-- Q の置換は最後の辺を厳密に保つ。 -/
lemma dgFourSimplexWithQ_lastEdge :
    (dgFourSimplexWithQ s Q).edgeHom 3 4 (by decide) = s.edgeHom 3 4 (by decide) :=
  SimplexData.replaceFixed_hom_of_ne _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by decide)

/-- Q の置換は最上位 rhs の既知部分を厳密に保つ。 -/
lemma dgFourSimplexWithQ_topResidual :
    dgFourSimplexTopResidual (dgFourSimplexWithQ s Q) = dgFourSimplexTopResidual s := by
  dsimp only [dgFourSimplexTopResidual, dgFourSimplexWithQ,
    SimplexData.edgeHom, SimplexData.tripleHom]
  rw [SimplexData.replaceFixed_hom_of_ne _ _ _ _ _ _ _ _ _ _
    {0, 2, 3, 4} 0 4 (-2) (by decide) (by decide) (by decide) (by decide) (by decide)]
  rw [SimplexData.replaceFixed_hom_of_ne _ _ _ _ _ _ _ _ _ _
    {1, 2, 3, 4} 1 4 (-2) (by decide) (by decide) (by decide) (by decide) (by decide)]
  rw [SimplexData.replaceFixed_hom_of_ne _ _ _ _ _ _ _ _ _ _
    {0, 1} 0 1 0 (by decide) (by decide) (by decide) (by decide) (by decide)]
  rw [SimplexData.replaceFixed_hom_of_ne _ _ _ _ _ _ _ _ _ _
    {0, 1, 3, 4} 0 4 (-2) (by decide) (by decide) (by decide) (by decide) (by decide)]
  rw [SimplexData.replaceFixed_hom_of_ne _ _ _ _ _ _ _ _ _ _
    {2, 3, 4} 2 4 (-1) (by decide) (by decide) (by decide) (by decide) (by decide)]
  rw [SimplexData.replaceFixed_hom_of_ne _ _ _ _ _ _ _ _ _ _
    {0, 1, 2} 0 2 (-1) (by decide) (by decide) (by decide) (by decide) (by decide)]
  rw [SimplexData.replaceFixed_hom_of_ne _ _ _ _ _ _ _ _ _ _
    {0, 1, 2, 4} 0 4 (-2) (by decide) (by decide) (by decide) (by decide) (by decide)]

/-- Q を挿入した実最上位 rhs は、既知残差と最後辺による Q の後合成の和。 -/
lemma dgFourSimplexWithQ_rhs_top :
    (dgFourSimplexWithQ s Q).rhs Finset.univ 0 4 (-3)
      (by decide) (by decide) (by decide) (by decide) =
      dgFourSimplexTopResidual s + compose A (s.edgeHom 3 4 (by decide)) Q (by decide) := by
  exact (dgFourSimplex_rhs_top (dgFourSimplexWithQ s Q)).trans
    (congrArg₂ (fun (f g : GradedHom A (s.obj 0) (s.obj 4) (-2)) => f + g)
      (dgFourSimplexWithQ_topResidual s Q)
      (congrArg₂ (fun (f : GradedHom A (s.obj 3) (s.obj 4) 0)
        (g : GradedHom A (s.obj 0) (s.obj 3) (-2)) => compose A f g (by decide))
          (dgFourSimplexWithQ_lastEdge s Q) (dgFourSimplexWithQ_component s Q)))

end SerrePositivity.InfinityCategories
