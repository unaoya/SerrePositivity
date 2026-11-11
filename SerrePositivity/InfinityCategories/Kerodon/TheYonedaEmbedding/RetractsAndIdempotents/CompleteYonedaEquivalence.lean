module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompleteYonedaRetracts
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionEquivalence

/-!
概要：冪等完備な元の ∞ 圏への冪等完備化は、元の Yoneda 因子化を順方向とする同値。
方針：元の Idem 内部の頂点同型を前層の表現可能性から充満忠実性で戻す。
規約：元の関手そのものを同値と判定する。一般の延長存在の代用にはしない。
使われ方：HTT 5.1.4.8 の表現可能な本質像からの回収。

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

/-- 元の圏が冪等完備なら、元の Idem の全対象は同じ Yoneda 因子化の本質像にある。 -/
lemma idemYoneda_isEssentiallySurjective_of_complete (C : SSet.{u}) [Quasicategory C]
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete C) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemYoneda C) := by
  intro F
  have hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsRetractPresheaf F.val := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex F
  obtain ⟨c, ⟨e⟩⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.isRetractPresheaf_iff_representable_of_complete hC F.val).mp hF
  refine ⟨ULift.up c, ⟨?_⟩⟩
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusionPresheaf_isFullyFaithful C).preimageVertexIso
  have he := congrArg
    (fun f : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C ↦
      f.app (Opposite.op ⦋0⦌) (ULift.up c)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemYoneda_inclusion C)
  exact he.symm ▸ e.symm

/-- 元の圏が冪等完備なら、元の Yoneda 因子化そのものは冪等完備化への同値。 -/
lemma idemYoneda_isQCatEquivalence_of_complete (C : SSet.{u}) [Quasicategory C]
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete C) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemYoneda C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemYoneda C)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemYoneda_isFullyFaithful C) (idemYoneda_isEssentiallySurjective_of_complete C hC)

/-- 元の Yoneda 因子化を順方向として保持する、冪等完備な元の圏とその冪等完備化の同値。 -/
def idemYonedaEquivalenceOfComplete (C : SSet.{u}) [Quasicategory C]
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj C) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Idem C) :=
  (idemYoneda_isQCatEquivalence_of_complete C hC).choose

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
