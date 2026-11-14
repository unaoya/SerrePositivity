module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.EffectiveIdempotents
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulCalculus

/-!
概要：元の全強分裂図式から有効な全 Idem 図式への元の制限は自明 Kan fibration。
方針：元の前合成の inner 性と充満忠実性を反映し、有効性から元の頂点全射性を証明する。
規約：標的全体の冪等完備性は要求せず、同じ元の全部分圏への制限そのものを判定する。
使われ方：HTT 4.4.5.16 の全強分裂空間の存在と coherent な一意性。

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

/-- 元の前合成の持ち上げは、元の全部分圏の包含の単射性により同じ制限へ反映される。 -/
lemma effectiveSplittingRestriction_hasLiftingProperty {A B X : SSet.{u}} (i : A ⟶ B)
    [HasLiftingProperty i (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.strongSplittingRestriction X)] :
    HasLiftingProperty i (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.effectiveSplittingRestriction X) := by
  constructor
  intro a b sq
  let j := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.effectiveIdempotents X).ι
  have sq' : CommSq a i (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.strongSplittingRestriction X) (b ≫ j) := by
    constructor
    calc
      a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.strongSplittingRestriction X = a ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.effectiveSplittingRestriction X ≫ j) :=
        congrArg (a ≫ ·) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.effectiveSplittingRestriction_inclusion X).symm
      _ = i ≫ (b ≫ j) := by rw [← Category.assoc, sq.w, Category.assoc]
  refine CommSq.HasLift.mk' { l := sq'.lift, fac_left := sq'.fac_left, fac_right := ?_ }
  apply (cancel_mono j).mp
  exact (Category.assoc _ _ _).trans
    ((congrArg (sq'.lift ≫ ·) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.effectiveSplittingRestriction_inclusion X)).trans sq'.fac_right)

/-- 元の有効図式への同じ制限は inner fibration。 -/
instance effectiveSplittingRestriction_innerFibration (X : SSet.{u}) [Quasicategory X] :
    InnerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.effectiveSplittingRestriction X) where
  mem := by
    intro A B i hi
    have : HasLiftingProperty i (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.strongSplittingRestriction X) := InnerFibration.mem i hi
    exact effectiveSplittingRestriction_hasLiftingProperty i

/-- 元の有効図式への同じ制限は、元の全写像空間で充満忠実。 -/
lemma effectiveSplittingRestriction_isFullyFaithful (X : SSet.{u}) [Quasicategory X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.effectiveSplittingRestriction X) := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.effectiveIdempotents X).ι :=
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _
  apply h.cancel_right
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.effectiveSplittingRestriction_inclusion]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.strongSplittingRestriction_isFullyFaithful X

/-- 元の有効な全図式は、その元の厳密な強い分裂により制限の頂点として回収される。 -/
lemma effectiveSplittingRestriction_surjective (X : SSet.{u}) :
    Function.Surjective ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.effectiveSplittingRestriction X).app (Opposite.op ⦋0⦌)) := by
  intro y
  have hy := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex y
  change Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IdemShape X).symm y.val)) at hy
  obtain ⟨s⟩ := hy
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s.val, Subtype.ext ?_⟩
  exact (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s.property).trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IdemShape X).apply_symm_apply y.val)

/-- 元の全強分裂図式から有効な全 Idem 図式への同じ制限は、自明 Kan fibration。 -/
lemma effectiveSplittingRestriction_trivialKanFibration (X : SSet.{u}) [Quasicategory X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.effectiveSplittingRestriction X) :=
  (effectiveSplittingRestriction_isFullyFaithful X).trivialKanFibration_of_surjective
    (effectiveSplittingRestriction_surjective X)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "4.4.5.16"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.effectiveSplittingRestriction_trivialKanFibration
