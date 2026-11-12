module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGTriangleResidualPrecompose
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.TruncatedTriangles

/-! # 指定三角形の始点の実閉細分

概要：実三角形の始点だけを元の閉射で細分し、二辺と三角 cochain を同じ射で前合成する。
方針：三角形データと閉前合成の微分式を使い、実二単体へ戻す。
規約：辺 12 を保持する。使われ方：最後外ホーンの指定三面の細分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 元の閉射による閉零 cycle の前合成も、同じ元の Hom 複体の閉零 cycle。 -/
def dgClosedCyclePrecompose {q x y : D} (c : _root_.SerrePositivity.DifferentialGraded.zeroCycles (_root_.SerrePositivity.DifferentialGraded.homObject A D x y))
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) :
    zeroCycles (homObject A D q y) := ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D 0 c.val s, by
  change (homObject A D q y).d 0 1 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D 0 c.val s) = 0
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose_d A D 0 1 rfl, c.property, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose_zero]⟩

/-- 指定三角形の始点だけを実閉射で細分した、三辺と三角 cochain のデータ。 -/
def dgTriangleSourceRefinement (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.TriangleData A D) (q : D)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (t.obj 0)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.TriangleData A D where
  obj := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.tripleObj q (t.obj 1) (t.obj 2)
  f01 := dgClosedCyclePrecompose t.f01 s
  f12 := t.f12
  f02 := dgClosedCyclePrecompose t.f02 s
  homotopy := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D (-1) t.homotopy s
  differential_homotopy := by
    have hd : (_root_.SerrePositivity.DifferentialGraded.homObject A D (t.obj 0) (t.obj 2)).d (-1) 0 t.homotopy =
        _root_.SerrePositivity.DifferentialGraded.compose A t.f12.val t.f01.val (by decide) - t.f02.val := t.differential_homotopy
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose_d A D (-1) 0 (by decide) t.homotopy s).trans
      ((congrArg (fun a : _root_.SerrePositivity.DifferentialGraded.GradedHom A (t.obj 0) (t.obj 2) 0 =>
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D 0 a s) hd).trans
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTriangleMissingResidual_precompose (closedHomEquiv A D _ _ s).val
            t.f01.val t.f02.val t.f12.val).symm)

/-- 指定三角形の始点だけを同じ実閉射で細分した、実際の二単体。 -/
def dgSimplexSourceRefinement (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 2) (q : D)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (t.obj 0)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 2 := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofTriangle (dgTriangleSourceRefinement t.toTriangle q s)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
