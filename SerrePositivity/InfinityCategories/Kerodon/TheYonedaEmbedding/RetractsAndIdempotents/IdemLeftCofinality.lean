module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.Cofinality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.QuillenALeft
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopy
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.LeftKanShapeIso
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Walking
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingLeftCommaContractibility

/-!
概要：元の全 Idem の元の強い分裂添字への包含は、極限を計算する向きにも cofinal。
方針：元の左 comma を元の slice の引き戻しへ同型で移し、Quillen A の left 側を使う。
規約：同じ元の包含と、元の全 Idem への射影を保持する。
使われ方：HTT 4.4.5.13 の元の強い分裂の指定錐の極限性。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の左 comma の nerve と元の slice 引き戻しの、指定した比較同型。 -/
def walkingLeftCommaSliceIso (P : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit.{u}) :
    nerve (CostructuredArrow _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingInclusion P) ≅
      pullback _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusion (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint P)) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveLeftKanShapeIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingInclusion P

/-- 元の比較同型は、元の全 Idem への射影と厳密に可換。 -/
lemma walkingLeftCommaSliceIso_projection (P : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit.{u}) :
    (walkingLeftCommaSliceIso P).hom ≫ pullback.fst _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusion
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint P)) =
        nerveMap (CostructuredArrow.proj _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingInclusion P) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveLeftKanShapeIso_hom_projection _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingInclusion P

/-- 元の包含に沿った元の slice の引き戻しは、各元の対象で弱可縮。 -/
lemma idemInclusion_slice_isWeaklyContractible (P : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (pullback _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusion (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint P))) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (walkingLeftCommaSliceIso P)).isWeakHomotopyEquivalence
  exact h.weaklyContractible_iff.mp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingLeftComma_isWeaklyContractible P)

/-- 元の全 Idem の元の強い分裂添字への包含は、極限を計算する向きにも cofinal。 -/
lemma idemInclusion_isLeftCofinal : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusion.{u} := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_of_weaklyContractible_slices
  intro b
  obtain ⟨P, rfl⟩ := (nerveEquiv (C := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit.{u})).symm.surjective b
  exact idemInclusion_slice_isWeaklyContractible P

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
