module

public import SerrePositivity.KST.Spectra.D3CompositeCorner

/-!
概要：実 loop 始点から相対 BF 対象への比較射を、全段 RLP を持つ比較へ精密化する。
方針：元の c_X 自体を相対 BF 分解し、同じ二因子・包含・補助単位を厳密回収する。
規約：元の実 loop 始点と比較は保持する。nativeLoop への全図式比較は別工程。
使われ方：比較射を含む全 Hom の RLP と厳密合成の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.NonConnective
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

/-- 元の実比較 c_X の相対 BF 中間対象。 -/
def commonRefinement (X : OmegaSpectrum.{u}) : OmegaSpectrum.{u} :=
  sequentialBFArrowMiddle (loopSourceComparison X)

/-- 元の実 loop 始点を保持する相対左脚。 -/
def commonLoopInclusion (X : OmegaSpectrum.{u}) : loopSource X ⟶ commonRefinement X :=
  sequentialBFArrowLeft (loopSourceComparison X)

/-- 相対 BF 対象 M_X へ戻る、全段 RLP を持つ元の比較右脚。 -/
def commonComparison (X : OmegaSpectrum.{u}) : commonRefinement X ⟶ middle X :=
  sequentialBFArrowRight (loopSourceComparison X)

/-- 実比較を選び直さず、同じ二因子で厳密回収する。 -/
@[reassoc]
lemma commonComparison_fac (X : OmegaSpectrum.{u}) :
    commonLoopInclusion X ≫ commonComparison X = loopSourceComparison X :=
  sequentialBFArrow_fac (loopSourceComparison X)

/-- 元の X から同じ共通 BF 対象への二段の左因子。 -/
def commonInclusion (X : OmegaSpectrum.{u}) : X ⟶ commonRefinement X :=
  loopSourceInclusion X ≫ commonLoopInclusion X

/-- 二段の左因子と比較右脚は元の相対 BF 包含を厳密回収する。 -/
@[reassoc]
lemma commonInclusion_comparison (X : OmegaSpectrum.{u}) :
    commonInclusion X ≫ commonComparison X = inclusion X := by
  rw [commonInclusion, Category.assoc, commonComparison_fac]
  exact OmegaSpectrum.Hom.ext (loopSourceComparison_left X)

/-- 補助標的への右脚は、同じ元の q_X の後合成。 -/
def commonProjection (X : OmegaSpectrum.{u}) :
    KanSequence.Hom (commonRefinement X).toKanSequence (target X) :=
  (⟨(commonComparison X).app, (commonComparison X).comm⟩ :
    KanSequence.Hom (commonRefinement X).toKanSequence (middle X).toKanSequence).comp (projection X)

/-- 元の実 loop 始点からの補助標的への右脚も厳密保持する。 -/
lemma commonLoopInclusion_projection (X : OmegaSpectrum.{u}) (n : ℕ) :
    (commonLoopInclusion X).app n ≫ (commonProjection X).app n =
      (loopSourceProjection X).app n := by
  change (commonLoopInclusion X).app n ≫
    ((commonComparison X).app n ≫ (projection X).app n) = _
  rw [← Category.assoc]
  change ((commonLoopInclusion X ≫ commonComparison X).app n) ≫ _ = _
  rw [commonComparison_fac, loopSourceComparison_right]

/-- 共通対象も同じ元の補助単位の二因子分解である。 -/
lemma commonProjection_fac (X : OmegaSpectrum.{u}) (n : ℕ) :
    (commonInclusion X).app n ≫ (commonProjection X).app n =
      (KanSequence.adjointLoopTailUnit X.toKanSequence).app n := by
  change (commonInclusion X).app n ≫ ((commonComparison X).app n ≫ (projection X).app n) = _
  rw [← Category.assoc]
  change (commonInclusion X ≫ commonComparison X).app n ≫ _ = _
  rw [commonInclusion_comparison, fac]

/-- 元の loop 始点を含める脚の相対 cofibration 性。 -/
lemma commonLoopInclusion_relative (X : OmegaSpectrum.{u}) :
    IsSequentialRelativeCofibration (commonLoopInclusion X) :=
  sequentialBFArrowLeft_isRelativeCofibration (loopSourceComparison X)

/-- 比較右脚の全段 RLP は元の相対 BF 分解から実証する。 -/
lemma commonComparison_rlp (X : OmegaSpectrum.{u}) (n : ℕ) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp ((commonComparison X).app n).right :=
  sequentialBFArrowRight_rlp (loopSourceComparison X) n

/-- 比較右脚自身の各段は全基点 π 同型。 -/
lemma commonComparison_levelwise (X : OmegaSpectrum.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((commonComparison X).app n).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _ (commonComparison_rlp X n)

/-- 元の実 loop 始点を保持する左脚も各段の全基点 π 同型。 -/
lemma commonLoopInclusion_levelwise (X : OmegaSpectrum.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((commonLoopInclusion X).app n).right := by
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp (g := ((commonComparison X).app n).right) _
    (commonComparison_levelwise X n)
  rw [← Under.comp_right]
  change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((commonLoopInclusion X ≫ commonComparison X).app n).right
  rw [commonComparison_fac]
  exact loopSourceComparison_levelwise X n

/-- 同じ元の包含を回収する二段左脚は、各段で全基点 π 同型。 -/
lemma commonInclusion_levelwise (X : OmegaSpectrum.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((commonInclusion X).app n).right :=
  (loopSourceInclusion_levelwise X n).comp (commonLoopInclusion_levelwise X n)

/-- 異なる X,Y に対する共通対象の比較 Hom corner の実全単射 RLP。 -/
lemma commonCorner_trivialKanFibration (X Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (RawSpectrumMapping.relativeCorner (commonInclusion X)
      (⟨(commonComparison Y).app, (commonComparison Y).comm⟩ :
        KanSequence.Hom (commonRefinement Y).toKanSequence (middle Y).toKanSequence)) :=
  RawSpectrumMapping.d3CompositeCorner_trivialKanFibration
    (loopSourceInclusion X) (commonLoopInclusion X) (loopSourceInclusion_relative X)
    (commonLoopInclusion_relative X) _ (commonComparison_rlp Y)

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
