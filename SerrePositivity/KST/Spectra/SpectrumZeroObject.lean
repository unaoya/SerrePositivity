module

public import SerrePositivity.KST.Spectra.PointedZeroMapping
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpectrumFiniteProducts
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentTerminal
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingSpaceModelEquivalence
public import SerrePositivity.InfinityCategories.F1B.InitialMappingSpace

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
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- 一点スペクトルから任意のスペクトルへの実際の射。 -/
def fromPoint (X : OmegaSpectrum.{u}) : spectrumPoint ⟶ X where
  app n := PointedObject.fromPoint (X.level n).space
  comm _ := suspensionPoint_isZero.eq_of_src _ _

/-- 一点スペクトルは通常の厳密なスペクトルの圏でも始対象。 -/
def point_isInitial : IsInitial spectrumPoint.{u} :=
  IsInitial.ofUniqueHom fromPoint
    (fun _ _ ↦ OmegaSpectrum.Hom.ext (fun _ ↦ PointedObject.point_isZero.eq_of_src _ _))

/-- 一点スペクトルは厳密なスペクトルの圏の零対象。 -/
lemma point_isZero : IsZero spectrumPoint.{u} where
  unique_to X := ⟨{ default := fromPoint X, uniq := fun f ↦ point_isInitial.hom_ext f _ }⟩
  unique_from X := ⟨{
    default := spectrumPoint_isTerminal.from X
    uniq := fun f ↦ spectrumPoint_isTerminal.hom_ext f _ }⟩

/-- 一点スペクトルによる、厳密なスペクトルの圏の零対象の存在。 -/
instance spectrumHasZeroObject : HasZeroObject OmegaSpectrum.{u} :=
  ⟨⟨spectrumPoint, point_isZero⟩⟩

/-- 零射は一点スペクトルを経由する射。 -/
instance spectrumHasZeroMorphisms : HasZeroMorphisms OmegaSpectrum.{u} :=
  point_isZero.hasZeroMorphisms

/-- 一点スペクトルからの全ての豊穣な写像空間は終対象。 -/
def pointMapping_isTerminal (X : OmegaSpectrum.{u}) :
    IsTerminal (mappingSpace spectrumPoint X) :=
  IsTerminal.ofUniqueHom (fun A ↦ toUnit A ≫ vertexOfHomMap (fromPoint X)) (fun A f ↦ by
    apply mapping_hom_ext
    intro n
    have : IsIso (spectrumPoint.{u}.level n).space.hom := by
      change IsIso (𝟙 (𝟙_ SSet.{u}))
      infer_instance
    exact (PointedZeroMapping.source_isTerminal _ _).hom_ext _ _)

/-- 一点スペクトルへの全ての豊穣な写像空間は終対象。 -/
def mappingPoint_isTerminal (X : OmegaSpectrum.{u}) :
    IsTerminal (mappingSpace X spectrumPoint) :=
  IsTerminal.ofUniqueHom
    (fun A ↦ toUnit A ≫ vertexOfHomMap (spectrumPoint_isTerminal.from X)) (fun A f ↦ by
      apply mapping_hom_ext
      intro n
      exact (PointedZeroMapping.target_isTerminal _ _ isTerminalTensorUnit).hom_ext _ _)

local instance zeroSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance zeroHomKan (X Y : OmegaSpectrum.{u}) : KanComplex (SimplicialCategory.sHom X Y) :=
  OmegaSpectrum.mappingSpace_kanComplex X Y

/-- 一点スペクトルの頂点は Sp の終対象。 -/
lemma point_isTerminalVertex : IsTerminalVertex
    (coherentNerveVertex spectrumPoint.{u}) :=
  coherentNerve_isTerminalVertex_of_enrichedTerminal _ mappingPoint_isTerminal

/-- 一点スペクトルの頂点は Sp の始対象。 -/
lemma point_isInitialVertex : IsInitialVertex
    (coherentNerveVertex spectrumPoint.{u}) := by
  apply isInitialVertex_of_pinchedHomLeft_isContractibleKan
  intro z
  obtain ⟨X, rfl⟩ := (coherentNerveVertexEquiv OmegaSpectrum.{u}).surjective z
  apply (pinchedHomLeftRightEquivalence _ _).symm.isContractibleKan
  exact (coherentHomEquivalence spectrumPoint X).isContractibleKan
    (ulift_isContractibleKan_of_isTerminal _ (pointMapping_isTerminal X))

/-- Sp 内の具体的な零頂点。 -/
def pointZeroVertex : ZeroVertex Sp.{u} where
  vertex := coherentNerveVertex spectrumPoint
  isInitial := point_isInitialVertex
  isTerminal := point_isTerminalVertex

/-- 元の Sp は零対象を持つ。 -/
instance sp_hasZeroVertex : HasZeroVertex Sp.{u} :=
  ⟨⟨pointZeroVertex.vertex, pointZeroVertex.isInitial, pointZeroVertex.isTerminal⟩⟩

end SerrePositivity.KST.Spectra.OmegaSpectrum
