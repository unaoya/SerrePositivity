module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Completion
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.MappingRetractContractibility

/-!
概要：元の冪等完備化の関手は、元の指定終対象を保存する。
方針：像同士の写像空間の可縮性を充満忠実性で移し、元の各対象の retract へ戻す。
規約：元の頂点の像そのものを終対象と判定する。
使われ方：HA 1.1.3.7 の冪等完備化の零対象。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の任意の冪等完備化は、同じ元の終対象の像を終対象へ送る。 -/
lemma IsIdempotentCompletion.map_isTerminalVertex {K C : SSet.{u}}
    [Quasicategory K] [Quasicategory C] (f : K ⟶ C) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f)
    {z : K _⦋0⦌} (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex z) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (f.app (Opposite.op ⦋0⦌) z) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isTerminalVertex_of_pinchedHom_isContractibleKan
  intro d
  obtain ⟨k, ⟨r⟩⟩ := hf.2.2 d
  exact r.pinchedHom_source_isContractibleKan _
    ((hf.2.1 k z).isContractibleKan_iff.mp (hz.pinchedHom_isContractibleKan k))

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
