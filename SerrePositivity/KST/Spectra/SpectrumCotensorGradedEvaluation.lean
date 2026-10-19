module

public import SerrePositivity.KST.Spectra.SpectrumCotensorCompatibleEnrichment

/-!
概要：cotensor の普遍評価を、全パラメータで自然な豊穣変換として束ねる。
方針：整合写像の二つの点つき豊穣射影と、評価の可換条件を使う。
規約：Mathlib の GradedNatTrans に実際の自然性の証明を与える。
使われ方：円の評価から coherent な loop 図式の族を構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
local instance gradedEvaluationSpectrumPointedEnrichment :
    EnrichedCategory PointedSimplicialSet.{u} OmegaSpectrum.{u} := pointedEnrichment

/-- 整合写像の元の射への点つき豊穣射影。 -/
def sourcePointedEnriched (A : PointedSimplicialSet.{u}) :
    EnrichedFunctor PointedSimplicialSet.{u} (Object A) OmegaSpectrum.{u} where
  obj X := X.val
  map X Y := sourceMap A X.val Y.val
  map_id X := identity_sourceMap A X.val
  map_comp X Y Z := composition_sourceMap A X.val Y.val Z.val

/-- 整合写像の cotensor 側への点つき豊穣射影。 -/
def cotensorPointedEnriched (A : PointedSimplicialSet.{u}) :
    EnrichedFunctor PointedSimplicialSet.{u} (Object A) OmegaSpectrum.{u} where
  obj X := cotensor A X.val
  map X Y := cotensorMap A X.val Y.val
  map_id X := identity_cotensorMap A X.val
  map_comp X Y Z := composition_cotensorMap A X.val Y.val Z.val

/-- 普遍評価は、二つの射影の間の A をパラメータとする豊穣自然変換。 -/
def gradedEvaluation (A : PointedSimplicialSet.{u}) :
    GradedNatTrans (Center.ofBraidedObj A) (cotensorPointedEnriched A)
      (sourcePointedEnriched A) where
  app X := cotensorEvaluation A X.val
  naturality X Y := ((condition_iff A X.val Y.val _ _).mp (condition A X.val Y.val)).symm

end SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
