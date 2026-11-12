module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGTetrahedronEquations
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FixedHomReplacement

/-! # 欠けた三角形 Q の挿入と最上位の右辺

概要：次数 −1 の未知成分を挿入し、既知の最上位残差と最後の閉辺の作用を厳密に回収する。
方針：固定一射の置換と、未知集合以外の成分の不変性を使う。
規約：全ての指定面を後段で保持する。使われ方：最後外三次ホーンの二未知方程式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
variable (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D 3) (Q : _root_.SerrePositivity.DifferentialGraded.GradedHom A (s.obj 0) (s.obj 2) (-1))

/-- 欠けた三角形成分だけを、型付きの指定 Q に置換する。 -/
def dgTetrahedronWithQ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D 3 :=
  s.replaceFixed {0, 1, 2} 0 2 (-1) (by decide) (by decide) (by decide) (by decide) Q

/-- 挿入した Q は、欠けた三角形成分そのもの。 -/
lemma dgTetrahedronWithQ_component :
    (dgTetrahedronWithQ s Q).tripleHom 0 1 2 (by decide) (by decide) = Q :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed_hom_same _ _ _ _ _ _ _ _ _ _

/-- 最後の閉辺は Q の挿入で変わらない。 -/
lemma dgTetrahedronWithQ_lastEdge :
    (dgTetrahedronWithQ s Q).edgeHom 2 3 (by decide) = s.edgeHom 2 3 (by decide) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed_hom_of_ne _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by decide)

/-- 最上位の既知残差は Q の挿入で変わらない。 -/
lemma dgTetrahedronWithQ_topResidual :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTetrahedronTopResidual (dgTetrahedronWithQ s Q) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTetrahedronTopResidual s := by
  have h₀₂₃ : (dgTetrahedronWithQ s Q).tripleHom 0 2 3 (by decide) (by decide) =
      s.tripleHom 0 2 3 (by decide) (by decide) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed_hom_of_ne _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by decide)
  have h₁₂₃ : (dgTetrahedronWithQ s Q).tripleHom 1 2 3 (by decide) (by decide) =
      s.tripleHom 1 2 3 (by decide) (by decide) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed_hom_of_ne _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by decide)
  have h₀₁ : (dgTetrahedronWithQ s Q).edgeHom 0 1 (by decide) =
      s.edgeHom 0 1 (by decide) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed_hom_of_ne _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by decide)
  have h₀₁₃ : (dgTetrahedronWithQ s Q).tripleHom 0 1 3 (by decide) (by decide) =
      s.tripleHom 0 1 3 (by decide) (by decide) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed_hom_of_ne _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by decide)
  exact congrArg₂ (fun (f g : GradedHom A (s.obj 0) (s.obj 3) (-1)) => f - g)
    (congrArg₂ (fun (f g : GradedHom A (s.obj 0) (s.obj 3) (-1)) => f - g) h₀₂₃
      (congrArg₂ (fun (f : GradedHom A (s.obj 1) (s.obj 3) (-1))
        (g : GradedHom A (s.obj 0) (s.obj 1) 0) => compose A f g (by decide)) h₁₂₃ h₀₁))
    h₀₁₃

/-- Q を挿入した最上位右辺は、既知残差に最後の閉辺と Q の合成を加えたもの。 -/
lemma dgTetrahedronWithQ_rhs_top :
    (dgTetrahedronWithQ s Q).rhs Finset.univ 0 3 (-2)
      (by decide) (by decide) (by decide) (by decide) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTetrahedronTopResidual s +
        _root_.SerrePositivity.DifferentialGraded.compose A (s.edgeHom 2 3 (by decide)) Q (by decide) := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTetrahedron_rhs_top (dgTetrahedronWithQ s Q)).trans
    (congrArg₂ (fun (f g : _root_.SerrePositivity.DifferentialGraded.GradedHom A (s.obj 0) (s.obj 3) (-1)) => f + g)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTetrahedronWithQ_topResidual s Q)
      (congrArg₂ (fun (f : _root_.SerrePositivity.DifferentialGraded.GradedHom A (s.obj 2) (s.obj 3) 0)
        (g : _root_.SerrePositivity.DifferentialGraded.GradedHom A (s.obj 0) (s.obj 2) (-1)) => _root_.SerrePositivity.DifferentialGraded.compose A f g (by decide))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTetrahedronWithQ_lastEdge s Q) (dgTetrahedronWithQ_component s Q)))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
