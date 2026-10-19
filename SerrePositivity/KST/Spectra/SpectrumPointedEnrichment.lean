module

public import SerrePositivity.KST.Spectra.RawSpectrumPointedAssociativity

/-!
概要：実際の BF Ω スペクトルの点つき単体集合による豊穣構造。
方針：元の全整合写像空間と、証明済みの単位・合成の法則を束ねる。
規約：合成のパラメータは smash。
使われ方：cotensor の普遍評価の高次自然性。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- 元の BF Hom の零写像の基点を保った豊穣構造。 -/
@[instance_reducible]
def pointedEnrichment : EnrichedCategory PointedSimplicialSet.{u} OmegaSpectrum.{u} where
  Hom X Y := RawSpectrumMapping.pointedSpace X Y.toKanSequence
  id := RawSpectrumMapping.pointedIdentity
  comp X Y Z := RawSpectrumMapping.pointedComposition X Y Z.toKanSequence
  id_comp X Y := RawSpectrumMapping.pointedIdentity_composition X Y.toKanSequence
  comp_id := RawSpectrumMapping.pointedComposition_identity
  assoc W X Y Z := RawSpectrumMapping.pointedComposition_assoc W X Y Z.toKanSequence

end SerrePositivity.KST.Spectra.OmegaSpectrum
