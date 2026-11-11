module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVertexIsoOfH0

/-! # Native dg nerve の通常の h と H⁰ の比較

概要：道の商による通常のホモトピー圏を全 dg 自然な H⁰ と比較する。
方針：二切断の辺の類への比較と既存の H⁰ 比較を合成する。
規約：三角関手性はまだ主張しない。使われ方：実 cofiber の対象条件と K(D) の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 通常の h N_dg(D) と全 dg 自然な H⁰(D) の比較同値。 -/
def dgStableHomotopyEquivalence :
    SSet.hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) ≌ DifferentialGraded.HomotopyCategory A D :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyCategoryBridge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.equivalence A D)

/-- 実頂点の比較像は、同じ dg 対象の H⁰ の像。 -/
lemma dgStableHomotopyEquivalence_obj_vertex (x : D) :
    (dgStableHomotopyEquivalence A D).functor.obj
      (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) =
        (_root_.SerrePositivity.DifferentialGraded.toHomotopy A D).obj (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) := rfl

/-- 実頂点の同型を H⁰ の同じ対象間の同型へ送る。 -/
def dgH0IsoOfVertexIso {x y : D}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) :
    (_root_.SerrePositivity.DifferentialGraded.toHomotopy A D).obj (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) ≅
      (_root_.SerrePositivity.DifferentialGraded.toHomotopy A D).obj (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) :=
  (dgStableHomotopyEquivalence A D).functor.mapIso e

end SerrePositivity.InfinityCategories.Project.DerivedCategories
