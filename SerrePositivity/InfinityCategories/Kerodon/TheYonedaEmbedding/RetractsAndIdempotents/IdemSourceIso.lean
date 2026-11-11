module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IdemCoconeRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SourceChains
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SourceSubcomplex
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Walking

/-!
概要：元の Idem と元の非分裂対象の全部分複体は、元の包含を保って同型。
方針：全次数の単射性と、全頂点条件からの元の全単体の復元を使う。
規約：同型の後の包含は元の Idem 包含そのもの。
使われ方：元の包含の厳密な inner 性と充満忠実性の入力の証明。

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

/-- 元の全部分複体への全 Idem の因子化は、全次数で全単射。 -/
lemma idemSourceLift_app_bijective (n : ℕ) :
    Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemSourceLift.{u}.app (Opposite.op ⦋n⦌)) := by
  constructor
  · intro a b h
    have hi : Function.Injective (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusion.{u}.app (Opposite.op ⦋n⦌)) :=
      (CategoryTheory.mono_iff_injective _).mp inferInstance
    exact hi (congrArg Subtype.val h)
  · intro F
    refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.sourceChain F.val (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.sourceSubcomplex_chain_vertex F), Subtype.ext ?_⟩
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.sourceChain_inclusion F.val (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.sourceSubcomplex_chain_vertex F)

/-- 元の全部分複体への因子化は、全単体の復元により同型。 -/
instance idemSourceLift_isIso : IsIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemSourceLift.{u} := by
  rw [NatTrans.isIso_iff_isIso_app]
  rintro ⟨⟨n⟩⟩
  exact (CategoryTheory.isIso_iff_bijective _).mpr (idemSourceLift_app_bijective n)

/-- 元の Idem と元の非分裂対象の全部分複体の、指定した因子化による同型。 -/
def idemSourceIso : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IdemShape.{u} ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.sourceSubcomplex := asIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemSourceLift

/-- 元の同型の後の全部分複体の包含は、元の全 Idem 包含そのもの。 -/
lemma idemSourceIso_inclusion : idemSourceIso.{u}.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.sourceSubcomplex.ι = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusion :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemSourceLift_inclusion

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
