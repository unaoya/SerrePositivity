module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Pointed

public import SerrePositivity.KST.Spectra.PointedZeroMapping
public import SerrePositivity.KST.Spectra.Limits.SpectrumFiniteProducts
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.CoherentTerminal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceModelEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialMappingSpace

/-!
概要：一点スペクトルの豊穣な始・終対象性と実際の Sp の零頂点。
方針：各段の点つき写像単体集合の終対象性を全切断へ移し、coherent nerve の Hom 比較を用いる。
規約：局所 Kan 性は既証のスペクトルの写像空間から得る。使われ方：HA §1.4.2、Sp の安定性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- 一点スペクトルから任意のスペクトルへの実際の射。 -/
def fromPoint (X : OmegaSpectrum.{u}) : _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint ⟶ X where
  app n := PointedObject.fromPoint (X.level n).space
  comm _ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.suspensionPoint_isZero.eq_of_src _ _

/-- 一点スペクトルは通常の厳密なスペクトルの圏でも始対象。 -/
def point_isInitial : IsInitial _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint.{u} :=
  IsInitial.ofUniqueHom fromPoint
    (fun _ _ ↦ OmegaSpectrum.Hom.ext (fun _ ↦ PointedObject.point_isZero.eq_of_src _ _))

/-- 一点スペクトルは厳密なスペクトルの圏の零対象。 -/
lemma point_isZero : IsZero _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint.{u} where
  unique_to X := ⟨{ default := fromPoint X, uniq := fun f ↦ point_isInitial.hom_ext f _ }⟩
  unique_from X := ⟨{
    default := _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint_isTerminal.from X
    uniq := fun f ↦ _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint_isTerminal.hom_ext f _ }⟩

/-- 一点スペクトルによる、厳密なスペクトルの圏の零対象の存在。 -/
instance spectrumHasZeroObject : HasZeroObject OmegaSpectrum.{u} :=
  ⟨⟨_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint, point_isZero⟩⟩

/-- 零射は一点スペクトルを経由する射。 -/
instance spectrumHasZeroMorphisms : HasZeroMorphisms OmegaSpectrum.{u} :=
  point_isZero.hasZeroMorphisms

/-- 一点スペクトルからの全ての豊穣な写像空間は終対象。 -/
def pointMapping_isTerminal (X : OmegaSpectrum.{u}) :
    IsTerminal (mappingSpace _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint X) :=
  IsTerminal.ofUniqueHom (fun A ↦ toUnit A ≫ vertexOfHomMap (fromPoint X)) (fun A f ↦ by
    apply mapping_hom_ext
    intro n
    have : IsIso (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint.{u}.level n).space.hom := by
      change IsIso (𝟙 (𝟙_ SSet.{u}))
      infer_instance
    exact (PointedZeroMapping.source_isTerminal _ _).hom_ext _ _)

/-- 一点スペクトルへの全ての豊穣な写像空間は終対象。 -/
def mappingPoint_isTerminal (X : OmegaSpectrum.{u}) :
    IsTerminal (mappingSpace X _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint) :=
  IsTerminal.ofUniqueHom
    (fun A ↦ toUnit A ≫ vertexOfHomMap (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint_isTerminal.from X)) (fun A f ↦ by
      apply mapping_hom_ext
      intro n
      exact (PointedZeroMapping.target_isTerminal _ _ isTerminalTensorUnit).hom_ext _ _)

local instance zeroSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance zeroHomKan (X Y : OmegaSpectrum.{u}) : KanComplex (SimplicialCategory.sHom X Y) :=
  OmegaSpectrum.mappingSpace_kanComplex X Y

/-- 一点スペクトルの頂点は Sp の終対象。 -/
lemma point_isTerminalVertex : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentNerve_isTerminalVertex_of_enrichedTerminal _ mappingPoint_isTerminal

/-- 一点スペクトルの頂点は Sp の始対象。 -/
lemma point_isInitialVertex : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint.{u}) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isInitialVertex_of_pinchedHomLeft_isContractibleKan
  intro z
  obtain ⟨X, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertexEquiv OmegaSpectrum.{u}).surjective z
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeftRightEquivalence _ _).symm.isContractibleKan
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomEquivalence _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint X).isContractibleKan
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ulift_isContractibleKan_of_isTerminal _ (pointMapping_isTerminal X))

/-- Sp 内の具体的な零頂点。 -/
def pointZeroVertex : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex Sp.{u} where
  vertex := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint
  isInitial := _root_.SerrePositivity.KST.Spectra.OmegaSpectrum.point_isInitialVertex
  isTerminal := _root_.SerrePositivity.KST.Spectra.OmegaSpectrum.point_isTerminalVertex

/-- 元の Sp は零対象を持つ。 -/
instance sp_hasZeroVertex : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex Sp.{u} :=
  ⟨⟨pointZeroVertex.vertex, pointZeroVertex.isInitial, pointZeroVertex.isTerminal⟩⟩

end SerrePositivity.KST.Spectra.OmegaSpectrum
