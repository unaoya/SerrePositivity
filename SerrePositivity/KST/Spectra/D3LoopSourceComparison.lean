module

public import SerrePositivity.KST.Spectra.D3LoopUnitExtension

/-!
概要：実 BF loop 始点から元の相対 BF 置換への比較射を二境界付きで構成する。
方針：実左因子と実右射影の corner に、元の包含と構成した単位延長を代入する。
規約：対象別の実比較。動く始点と全 loop 図式の自然性は別途必要。
使われ方：d3b② の c_X と a_X≫c_X=i_X、c_X≫q_X=r_X の厳密回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance loopSourceComparisonSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 元の左包含と同じ補助単位の延長を同時に指定する実 corner 境界。 -/
def loopSourceComparisonBoundary (X : OmegaSpectrum.{u}) :
    𝟙_ SSet.{u} ⟶ RawSpectrumMapping.relativeCornerTarget
      (loopSourceInclusion X) (projection X) :=
  pullback.lift
    (RawSpectrumMapping.d3VertexMap X (middle X).toKanSequence
      ⟨(inclusion X).app, (inclusion X).comm⟩)
    (RawSpectrumMapping.d3VertexMap (loopSource X) (target X) (loopSourceProjection X)) (by
      rw [RawSpectrumMapping.d3VertexMap_post, RawSpectrumMapping.d3VertexMap_pre]
      congr 1
      apply KanSequence.Hom.ext_app
      intro n
      exact (fac X n).trans (loopSourceProjection_fac X n).symm)

/-- 指定二境界を持つ元の corner の実切断。 -/
def loopSourceComparisonSection (X : OmegaSpectrum.{u}) :
    RawSpectrumMapping.relativeCornerTarget (loopSourceInclusion X) (projection X) ⟶
      RawSpectrumMapping.space (loopSource X) (middle X).toKanSequence := by
  let := comparisonCorner_trivialKanFibration X (loopSourceInclusion X)
    (loopSourceInclusion_relative X)
  exact Classical.choose
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (comparisonCorner X (loopSourceInclusion X)))

/-- 同じ切断は元の左右二境界を全単体で厳密に回収する。 -/
lemma loopSourceComparisonSection_fac (X : OmegaSpectrum.{u}) :
    loopSourceComparisonSection X ≫ comparisonCorner X (loopSourceInclusion X) = 𝟙 _ := by
  let := comparisonCorner_trivialKanFibration X (loopSourceInclusion X)
    (loopSourceInclusion_relative X)
  exact Classical.choose_spec
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (comparisonCorner X (loopSourceInclusion X)))

/-- 指定包含と元の単位延長の両境界を満たす、同じ全 Hom 内の実比較点。 -/
def loopSourceComparisonFamily (X : OmegaSpectrum.{u}) :
    𝟙_ SSet.{u} ⟶ RawSpectrumMapping.space (loopSource X) (middle X).toKanSequence :=
  loopSourceComparisonBoundary X ≫ loopSourceComparisonSection X

/-- 同じ比較族の左境界は元の包含そのもの。 -/
lemma loopSourceComparisonFamily_left (X : OmegaSpectrum.{u}) :
    loopSourceComparisonFamily X ≫
      RawSpectrumMapping.pre (loopSourceInclusion X) (middle X).toKanSequence =
    RawSpectrumMapping.d3VertexMap X (middle X).toKanSequence
      ⟨(inclusion X).app, (inclusion X).comm⟩ := by
  have h := congrArg (· ≫ pullback.fst _ _) (loopSourceComparisonSection_fac X)
  simp only [comparisonCorner, Category.assoc, RawSpectrumMapping.relativeCorner_fst,
    Category.id_comp] at h
  dsimp only [loopSourceComparisonFamily, loopSourceComparisonBoundary]
  rw [Category.assoc, h, pullback.lift_fst]

/-- 同じ比較族の右境界は構成した単位延長そのもの。 -/
lemma loopSourceComparisonFamily_right (X : OmegaSpectrum.{u}) :
    loopSourceComparisonFamily X ≫ RawSpectrumMapping.post (loopSource X) (projection X) =
      RawSpectrumMapping.d3VertexMap (loopSource X) (target X) (loopSourceProjection X) := by
  have h := congrArg (· ≫ pullback.snd _ _) (loopSourceComparisonSection_fac X)
  simp only [comparisonCorner, Category.assoc, RawSpectrumMapping.relativeCorner_snd,
    Category.id_comp] at h
  dsimp only [loopSourceComparisonFamily, loopSourceComparisonBoundary]
  rw [Category.assoc, h, pullback.lift_snd]

/-- 元の全 Hom の比較点から取り出す、実 BF 比較射 c_X。 -/
def loopSourceComparison (X : OmegaSpectrum.{u}) : loopSource X ⟶ middle X := by
  let f := RawSpectrumMapping.d3HomOfVertex (loopSource X) (middle X).toKanSequence
    ((RawSpectrumMapping.space (loopSource X) (middle X).toKanSequence).unitHomEquiv
      (loopSourceComparisonFamily X))
  exact ⟨f.app, f.comm⟩

/-- 実比較射は指定左包含を各段で厳密に保つ。 -/
lemma loopSourceComparison_left (X : OmegaSpectrum.{u}) (n : ℕ) :
    (loopSourceInclusion X).app n ≫ (loopSourceComparison X).app n = (inclusion X).app n := by
  have h := congrArg ((RawSpectrumMapping.space X (middle X).toKanSequence).unitHomEquiv)
    (loopSourceComparisonFamily_left X)
  rw [unitHomEquiv_comp] at h
  have hp := RawSpectrumMapping.d3HomOfVertex_pre (loopSourceInclusion X)
    (middle X).toKanSequence
    ((RawSpectrumMapping.space (loopSource X) (middle X).toKanSequence).unitHomEquiv
      (loopSourceComparisonFamily X)) n
  rw [h, RawSpectrumMapping.d3HomOfVertex_app, RawSpectrumMapping.d3VertexMap_evaluation] at hp
  simpa only [OmegaSpectrum.toKanSequence, Equiv.symm_apply_apply,
    loopSourceComparison] using hp.symm

/-- 実比較射は指定右射影も各段で厳密に保つ。 -/
lemma loopSourceComparison_right (X : OmegaSpectrum.{u}) (n : ℕ) :
    (loopSourceComparison X).app n ≫ (projection X).app n = (loopSourceProjection X).app n := by
  have h := congrArg ((RawSpectrumMapping.space (loopSource X) (target X)).unitHomEquiv)
    (loopSourceComparisonFamily_right X)
  rw [unitHomEquiv_comp] at h
  have hp := RawSpectrumMapping.d3HomOfVertex_post (loopSource X) (projection X)
    ((RawSpectrumMapping.space (loopSource X) (middle X).toKanSequence).unitHomEquiv
      (loopSourceComparisonFamily X)) n
  rw [h, RawSpectrumMapping.d3HomOfVertex_app, RawSpectrumMapping.d3VertexMap_evaluation] at hp
  simpa only [OmegaSpectrum.toKanSequence, Equiv.symm_apply_apply,
    loopSourceComparison] using hp.symm

/-- 元の二境界を保つ比較選択 fiber 自体が可縮。自由な可逆辺の追加ではない。 -/
lemma loopSourceComparisonFiber_isContractibleKan (X : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (comparisonFiber X (loopSourceInclusion X)
      ((RawSpectrumMapping.relativeCornerTarget (loopSourceInclusion X) (projection X)).unitHomEquiv
        (loopSourceComparisonBoundary X))) :=
  comparisonFiber_isContractibleKan X (loopSourceInclusion X) (loopSourceInclusion_relative X) _

/-- 実比較 c_X は各段で元の全基点 π 同型。 -/
lemma loopSourceComparison_levelwise (X : OmegaSpectrum.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((loopSourceComparison X).app n).right := by
  apply (_root_.SerrePositivity.KST.Spectra.KanPiIsomorphism.cancel_left_atVertex (loopSourceInclusion_levelwise X n))
    (x := PointedSimplicialSet.basepoint (X.level n).space)
  rw [← Under.comp_right, loopSourceComparison_left]
  exact inclusion_levelwise X n

/-- 選択した二境界付き比較射そのものが元の Sp の可逆辺。 -/
lemma loopSourceComparison_isInvertible (X : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (loopSourceComparison X)) :=
  SpectrumMappingAcyclic.isInvertible_of_levelwise _ (loopSourceComparison_levelwise X)

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
