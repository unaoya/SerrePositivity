module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRestrictionArrowReflection
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStableHomotopyEdges
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedEdges

/-! # 元の実合成二単体の代表加群の主導来像

概要：元の実辺を代表加群の導来射へ送り、指定実二単体の三辺の合成式を保つ。
方針：通常の h と H⁰ の実辺の比較から代表加群への反映を使う。
規約：前三角性も平坦性も不要。使われ方：共通実分母による全次数の同時零化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 元の実辺の閉射を代表加群の主導来射へ送る。 -/
def dgRepresentableDerivedEdgeMap {x y : D}
    (f : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableDerivedMap A D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed f)

/-- 指定された実二単体の合成等式は、代表加群の主導来圏でも成立する。 -/
lemma dgRepresentableDerivedEdgeMap_compStruct {x y z : D}
    {f : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)}
    {g : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex z)}
    {k : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex z)} (c : Truncated.Edge.CompStruct f g k) :
    dgRepresentableDerivedEdgeMap A D f ≫ dgRepresentableDerivedEdgeMap A D g =
      dgRepresentableDerivedEdgeMap A D k := by
  have h := congrArg (fun a => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence A D).functor.map a)
    (Truncated.HomotopyCategory.homMk_comp_homMk c)
  rw [Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence_map_homMk,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence_map_homMk, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence_map_homMk] at h
  have he := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableDerivedMap_eq_iff A D
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed f ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed g) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed k)).mpr
      (by simpa only [Functor.map_comp] using h)
  simpa only [dgRepresentableDerivedEdgeMap, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableDerivedMap,
    Functor.map_comp] using he

end SerrePositivity.InfinityCategories.Project.DerivedCategories
