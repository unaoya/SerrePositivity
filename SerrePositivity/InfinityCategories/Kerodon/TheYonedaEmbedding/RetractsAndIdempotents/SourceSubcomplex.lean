module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalVertices
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Walking
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingClassification

/-!
概要：元の非分裂対象だけを頂点とする全部分複体を構成する。
方針：元の Idem 包含を全頂点条件で因子化し、全単体の各対象の条件を回収する。
規約：元の全包含を、元の全部分複体の包含後に厳密に回収する。
使われ方：元の Idem 包含の inner fibration 性と写像空間の充満忠実性。

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

/-- 元の分裂添字の頂点が、元の非分裂対象であるという条件。 -/
def IsSourceVertex (v : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SplitShape.{u} _⦋0⦌) : Prop := v.obj 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSource

/-- 元の非分裂対象を頂点とする元の全部分複体。 -/
def sourceSubcomplex : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SplitShape.{u}.Subcomplex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SplitShape IsSourceVertex

/-- 元の Idem 包含の各頂点は、元の非分裂対象そのもの。 -/
lemma idemInclusion_source_vertex (a : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IdemShape.{u} _⦋0⦌) :
    IsSourceVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusion.app (Opposite.op ⦋0⦌) a) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingInclusion.obj (a.obj 0) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSource
  exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingInclusion.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingObject_eq (a.obj 0))

/-- 元の Idem 包含を、元の非分裂対象の全部分複体へ全単体ごと持ち上げる。 -/
def idemSourceLift : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IdemShape.{u} ⟶ sourceSubcomplex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift IsSourceVertex _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusion idemInclusion_source_vertex

/-- 元の全部分複体の包含の後で、元の全 Idem 包含を厳密に回収する。 -/
lemma idemSourceLift_inclusion : idemSourceLift.{u} ≫ sourceSubcomplex.ι = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusion :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 元の全部分複体の全単体の全対象は、元の非分裂対象そのもの。 -/
lemma sourceSubcomplex_chain_vertex {n : ℕ} (F : sourceSubcomplex.{u}.toSSet _⦋n⦌)
    (i : Fin (n + 1)) : F.val.obj i = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSource :=
  F.property (SimplexCategory.const ⦋0⦌ ⦋n⦌ i)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
