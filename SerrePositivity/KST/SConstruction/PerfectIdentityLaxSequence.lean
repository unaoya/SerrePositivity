module
public import SerrePositivity.KST.SConstruction.PerfectLaxCategory
public import SerrePositivity.KST.SConstruction.PerfectVerdierPresentation
public import SerrePositivity.KST.LocalizingInvariants.IdentityLaxVerdier

/-! # 恒等 lax 差の Cat^perf Verdier 列
概要：元の対角と cofiber 差の列を、同じ完備な右端で Cat^perf の提示列にする。
方針：恒等 lax 圏の完備性を証明し、右端の恒等関手を冪等完備化として使う。
規約：元の対角・差・零角を保持する。使われ方：LT の二つの fiber 列の比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories LocalizingInvariants
open scoped Simplicial

/-- 元の対角と差を持つ恒等 lax 列の、同じ Cat^perf 提示。 -/
def perfectIdentityLaxSequence (Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) (hQ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete Q.obj) :
    PerfectVerdierSequence.{u} where
  verdier := IdentityLax.verdierSequence Q
  left_complete := hQ
  middle_complete := perfectLaxCategory_isIdempotentComplete (𝟙 Q) (𝟙 Q) hQ hQ
  right := Q
  completion := ⟨𝟙 Q.obj, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_id Q.obj⟩
  isCompletion := ⟨hQ, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isFullyFaithful_id _, by
    intro x
    exact ⟨x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf.refl x⟩⟩

/-- 同じ提示列の射影は、元の恒等 lax 差を厳密に回収する。 -/
lemma perfectIdentityLaxSequence_projection (Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u})
    (hQ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete Q.obj) :
    (perfectIdentityLaxSequence Q hQ).projection = exactLaxDifference (𝟙 Q) (𝟙 Q) := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.ext
  exact Category.comp_id _

/-- 同じ元の安定圏値四角形は、元の対角・零角・差の辺を保持する。 -/
lemma perfectIdentityLaxRawSquare_edges (Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u})
    (hQ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete Q.obj) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ perfectVerdierRawSquare (perfectIdentityLaxSequence Q hQ) =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (IdentityLax.exactDiagonal Q)).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ perfectVerdierRawSquare (perfectIdentityLaxSequence Q hQ) =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (fromZeroCategory Q)).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ perfectVerdierRawSquare (perfectIdentityLaxSequence Q hQ) =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory Q)).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ perfectVerdierRawSquare (perfectIdentityLaxSequence Q hQ) =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (exactLaxDifference (𝟙 Q) (𝟙 Q))).edge := by
  have h := perfectVerdierRawSquare_edges (perfectIdentityLaxSequence Q hQ)
  rw [perfectIdentityLaxSequence_projection] at h
  exact h

end SerrePositivity.KST.SConstruction
