module

public import SerrePositivity.KST.Spectra.RawSpectrumCotensorIso
public import SerrePositivity.KST.Spectra.RawSpectrumMappingAcyclic

/-!
概要：実際の BF cotensor の豊穣写像空間を、元の全写像空間の点つき内部 Hom と比較する。
方針：BF 置換射影の後合成の同値に、全整合族の厳密な cotensor 交換同型を合成する。
規約：全ての点つき源 A を扱い、弱同値を追加仮定にしない。使われ方：Sp の loop の普遍性。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- BF cotensor の実際の豊穣 Hom と、元の全写像空間の内部 Hom の同値。 -/
def cotensorMappingEquivalence (X Y : OmegaSpectrum.{u}) (A : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (mappingSpace X (cotensor A Y))
      (PointedObject.basedHom A (RawSpectrumMapping.pointedSpace X Y.toKanSequence)).right :=
  (RawSpectrumMapping.cotensorProjectionEquivalence X Y A).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (PointedSimplicialSet.forget.mapIso
      (RawSpectrumMapping.cotensorIso X Y.toKanSequence A)))

/-- 比較の順写像は元の BF 置換射影と構成した源交換による。 -/
lemma cotensorMappingEquivalence_hom (X Y : OmegaSpectrum.{u})
    (A : PointedSimplicialSet.{u}) :
    (cotensorMappingEquivalence X Y A).hom =
      RawSpectrumMapping.post X (cotensorProjection A Y) ≫
        (RawSpectrumMapping.cotensorComparison X Y.toKanSequence A).right := rfl

/-- 同じ実際の比較射は Kan 複体の単体的ホモトピー同値でもある。 -/
lemma cotensorMappingComparison_homotopyEquivalence (X Y : OmegaSpectrum.{u})
    (A : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (cotensorMappingEquivalence X Y A).hom :=
  (cotensorMappingEquivalence X Y A).isQCatEquivalence.isSimplicialHomotopyEquivalence

end SerrePositivity.KST.Spectra.OmegaSpectrum
