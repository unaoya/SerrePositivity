module

public import SerrePositivity.InfinityCategories.F2.Idempotent.MappingRetractContractibility
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeInitialBoundaryCriterion
public import SerrePositivity.InfinityCategories.Stable.Pointed

/-!
概要：元の終対象・始対象・零対象の指定 retract も、同じ元の圏内で普遍対象。
方針：元の全 pinched Hom の可縮性を、指定 retract による前後合成で戻す。
規約：同じ元の頂点を保持し、同型な別の頂点の存在だけで代用しない。
使われ方：双カルテジアンな零角四角形の全 coherent 分裂。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の終対象の指定 retract は、元の同じ頂点で終対象。 -/
lemma isTerminalVertex_of_vertexRetraction {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (r : VertexRetraction x y) (hy : IsTerminalVertex y) :
    IsTerminalVertex x := by
  apply isTerminalVertex_of_pinchedHom_isContractibleKan
  intro z
  exact r.pinchedHom_target_isContractibleKan z (hy.pinchedHom_isContractibleKan z)

/-- 元の始対象の指定 retract は、元の同じ頂点で始対象。 -/
lemma isInitialVertex_of_vertexRetraction {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (r : VertexRetraction x y) (hy : IsInitialVertex y) :
    IsInitialVertex x := by
  apply F1B.kanIsInitialVertex_of_pinchedHom_isContractibleKan
  intro z
  exact r.pinchedHom_source_isContractibleKan z
    (F1B.kanInitialVertex_pinchedHom_isContractibleKan hy z)

/-- 元の零対象の指定 retract は、元の同じ頂点で零対象。 -/
lemma isZeroVertex_of_vertexRetraction {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (r : VertexRetraction x y) (hy : IsZeroVertex y) : IsZeroVertex x :=
  ⟨isInitialVertex_of_vertexRetraction r hy.1, isTerminalVertex_of_vertexRetraction r hy.2⟩

end SerrePositivity.InfinityCategories.F2.Idempotent
