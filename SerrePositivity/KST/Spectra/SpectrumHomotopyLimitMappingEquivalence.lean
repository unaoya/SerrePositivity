module

public import SerrePositivity.KST.Spectra.RawSpectrumHomotopyLimitIso
public import SerrePositivity.KST.Spectra.RawSpectrumMappingAcyclic
public import SerrePositivity.KST.Spectra.SpectrumHomotopyLimitCone

/-!
概要：元の BF homotopy limit の豊穣 Hom は、元の点つき Hom の homotopy end に同値。
方針：BF 射影による後合成の全単射 RLP と、元の Kan 列の Hom-end 交換同型を合成する。
規約：任意の小さい通常図式、全パラメータを扱う。使われ方：Sp の ∞ 極限性と γ3 の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
variable {I : Type u} [SmallCategory I]
local instance homotopyMappingCoefficientKan (X : OmegaSpectrum.{u})
    (D : I ⥤ OmegaSpectrum.{u}) (i : I) :
    KanComplex ((((D ⋙ forgetToKan) ⋙ RawSpectrumMapping.pointedFunctor X).obj i).right) :=
  RawSpectrumMapping.pointedSpace_kanComplex X (D.obj i).toKanSequence

/-- BF homotopy limit の射影は、元の豊穣 Hom 上でも実際の同値を誘導する。 -/
def homotopyLimitProjectionMappingEquivalence (X : OmegaSpectrum.{u})
    (D : I ⥤ OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (mappingSpace X (homotopyLimit D))
      (RawSpectrumMapping.space X (KanSequence.homotopyLimit (D ⋙ forgetToKan))) := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (RawSpectrumMapping.post X (homotopyLimitProjection D)) :=
    RawSpectrumMapping.post_trivialKanFibration X _ (fun n ↦
      (KanSequence.replacementStage (KanSequence.homotopyLimit (D ⋙ forgetToKan)) n).projection_rlp)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration (RawSpectrumMapping.post X (homotopyLimitProjection D))

/-- 元の BF homotopy limit の実際の Hom と、元の全 Hom を係数とする homotopy end の同値。 -/
def homotopyLimitMappingEquivalence (X : OmegaSpectrum.{u}) (D : I ⥤ OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (mappingSpace X (homotopyLimit D))
      (PointedWeightedEnd.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
        ((D ⋙ forgetToKan) ⋙ RawSpectrumMapping.pointedFunctor X)).right :=
  (homotopyLimitProjectionMappingEquivalence X D).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (PointedSimplicialSet.forget.mapIso
      (RawSpectrumMapping.homotopyLimitIso X (D ⋙ forgetToKan))))

/-- 同値の順射は BF 射影の後合成と、元の Hom-end 交換の合成そのもの。 -/
lemma homotopyLimitMappingEquivalence_hom (X : OmegaSpectrum.{u})
    (D : I ⥤ OmegaSpectrum.{u}) :
    (homotopyLimitMappingEquivalence X D).hom =
      RawSpectrumMapping.post X (homotopyLimitProjection D) ≫
        (RawSpectrumMapping.homotopyLimitIso X (D ⋙ forgetToKan)).hom.right := rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum
