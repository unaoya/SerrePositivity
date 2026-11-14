module
public import SerrePositivity.KST.SConstruction.PerfectStableInfinity
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagrams
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.FullSubcomplexEdgeLift

/-! # Cat^perf の同じ完全関手の実辺
概要：冪等完備な両端を持つ完全関手を、元の一単体を保つ Cat^perf の辺へ持ち上げる。
方針：全部分複体への両端点を指定した辺の持ち上げを用いる。
規約：ホモトピー類の代表を選び直さない。使われ方：局所化不変量の元の二辺の像。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories LocalizingInvariants

open scoped Simplicial

/-- Cat^perf の包含は、元の全部分複体の単射をそのまま持つ。 -/
instance perfectStableInfinityInclusion_mono : Mono perfectStableInfinityInclusion.{u} :=
  inferInstanceAs (Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity perfectStableVertexPredicate).ι)

/-- 同じ実完全関手の元の辺を持つ、Cat^perf の両端指定の辺。 -/
def perfectStableArrow {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B)
    (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete A.obj) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete B.obj) :
    perfectStableInfinity.{u}.Edge (perfectStableVertex A hA) (perfectStableVertex B hB) :=
  SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullSubcomplexEdgeLift perfectStableVertexPredicate
    (perfectStableVertex A hA) (perfectStableVertex B hB) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow F).edge
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow F).src_eq (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow F).tgt_eq)

/-- Cat^perf の同じ辺を含めると、元の完全関手の辺を厳密に回収する。 -/
lemma perfectStableArrow_inclusion {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B)
    (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete A.obj) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete B.obj) :
    SSet.yonedaEquiv.symm (perfectStableArrow F hA hB).edge ≫
        perfectStableInfinityInclusion = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow F).edge := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rfl

end SerrePositivity.KST.SConstruction
