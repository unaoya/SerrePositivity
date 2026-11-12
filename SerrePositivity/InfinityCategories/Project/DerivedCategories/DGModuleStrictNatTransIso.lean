module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleStrictNatTrans
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictNatTransVertex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleNerveHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise

/-! # 全 Hom 自然な加群同型族による実関手同型

概要：全次数で自然な閉加群同型族は native dg nerve の関手同型を与える。
方針：実ホモトピーの頂点辺を指定 cycle の辺と同定し、同型性を反映する。
規約：単体的ホモトピー自体を使う。使われ方：延長と Yoneda の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A E] [Small.{u} E]
variable {D : Type (max (u + 1) v)} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
variable {F G : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D (_root_.SerrePositivity.DifferentialGraded.RightModule A E)}
variable (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
variable (a : ∀ x, ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (F.obj x) ⟶
  ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (G.obj x))
variable (hc : ∀ x, η.app x = _root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) (a x)))
include hc

/-- 指定した実同型の cycle を成分に持つホモトピーは全実頂点で可逆。 -/
lemma dgModuleStrictNatTrans_pointwise (ha : ∀ x, IsIso (a x))
    (z : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge η.homotopy z).toTruncated := by
  obtain ⟨x, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective z
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTrans_homotopy_vertex_edge η x
  rw [hc x] at he
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr
  have := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge_isIso_of_homotopy A E (a x) (by
    let := ha x
    infer_instance)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeToPathHomotopyCategory _).map_isIso
    (SSet.Truncated.HomotopyCategory₂.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A E (a x)).toTruncated)

/-- 実加群同型を成分に持つ厳密自然変換を実関手圏の同型へ束ねる。 -/
def dgModuleFunctorIsoOfStrictNatTrans (ha : ∀ x, IsIso (a x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy η.homotopy
    (dgModuleStrictNatTrans_pointwise A E η a hc ha)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
