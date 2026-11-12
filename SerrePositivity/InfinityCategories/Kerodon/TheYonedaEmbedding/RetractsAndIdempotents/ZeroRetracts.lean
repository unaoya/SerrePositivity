module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.MappingRetractContractibility
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeInitialBoundaryCriterion
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Pointed

/-!
概要：元の終対象・始対象・零対象の指定 retract も、同じ元の圏内で普遍対象。
方針：元の全 pinched Hom の可縮性を、指定 retract による前後合成で戻す。
規約：同じ元の頂点を保持し、同型な別の頂点の存在だけで代用しない。
使われ方：双カルテジアンな零角四角形の全 coherent 分裂。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の終対象の指定 retract は、元の同じ頂点で終対象。 -/
lemma isTerminalVertex_of_vertexRetraction {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (r : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetraction x y) (hy : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isTerminalVertex_of_pinchedHom_isContractibleKan
  intro z
  exact r.pinchedHom_target_isContractibleKan z (hy.pinchedHom_isContractibleKan z)

/-- 元の始対象の指定 retract は、元の同じ頂点で始対象。 -/
lemma isInitialVertex_of_vertexRetraction {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (r : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetraction x y) (hy : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsInitialVertex_of_pinchedHom_isContractibleKan
  intro z
  exact r.pinchedHom_source_isContractibleKan z
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanInitialVertex_pinchedHom_isContractibleKan hy z)

/-- 元の零対象の指定 retract は、元の同じ頂点で零対象。 -/
lemma isZeroVertex_of_vertexRetraction {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (r : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetraction x y) (hy : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex y) : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex x :=
  ⟨isInitialVertex_of_vertexRetraction r hy.1, isTerminalVertex_of_vertexRetraction r hy.2⟩

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
