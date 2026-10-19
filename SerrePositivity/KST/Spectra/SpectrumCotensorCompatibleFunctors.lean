module

public import SerrePositivity.KST.Spectra.SpectrumCotensorCompatibleEnrichment
public import SerrePositivity.KST.Spectra.RawSpectrumPointedCompositionComparison

/-!
概要：整合写像の圏から元の BF 対象と cotensor への二つの豊穣関手。
方針：二つの射影の単位・合成保存を、元の単体的合成との比較に沿い忘却する。
規約：選んだ cotensorPost の法則を使わない。使われ方：coherent な cotensor 関手。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra
namespace RawSpectrumMapping

/-- 点つき豊穣単位の非基点側は元の BF 恒等射の頂点。 -/
lemma pointedIdentity_underlying (X : OmegaSpectrum.{u}) :
    PointedSimplicialSet.forgetUnit ≫ (pointedIdentity X).right =
      OmegaSpectrum.mappingIdentity X := by
  rw [PointedSimplicialSet.forgetUnit_comp]
  apply (OmegaSpectrum.mappingSpace X X).unitHomEquiv.injective
  change PointedSimplicialSet.unitVertexEquiv _ (pointedIdentity X) = _
  rw [pointedIdentity, Equiv.apply_symm_apply]
  rfl

end RawSpectrumMapping
namespace OmegaSpectrum.CotensorCompatible
local instance compatibleFunctorsSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 元の BF 対象と元の射への射影は、実際の単体的豊穣関手。 -/
def sourceEnriched (A : PointedSimplicialSet.{u}) :
    EnrichedFunctor SSet.{u} (Object A) OmegaSpectrum.{u} where
  obj X := X.val
  map X Y := (sourceMap A X.val Y.val).right
  map_id X := by
    change (PointedSimplicialSet.forgetUnit ≫ (identity A X.val).right) ≫
      (sourceMap A X.val X.val).right = _
    rw [Category.assoc, ← Under.comp_right, identity_sourceMap,
      RawSpectrumMapping.pointedIdentity_underlying]
    rfl
  map_comp X Y Z := by
    change (PointedSimplicialSet.productToSmash _ _ ≫
      (composition A X.val Y.val Z.val).right) ≫ (sourceMap A X.val Z.val).right = _
    rw [Category.assoc, ← Under.comp_right, composition_sourceMap, Under.comp_right,
      ← Category.assoc, ← PointedSimplicialSet.productToSmash_naturality,
      Category.assoc, RawSpectrumMapping.productToSmash_pointedComposition]
    rfl

/-- cotensor の対象と整合する射への射影も、実際の単体的豊穣関手。 -/
def cotensorEnriched (A : PointedSimplicialSet.{u}) :
    EnrichedFunctor SSet.{u} (Object A) OmegaSpectrum.{u} where
  obj X := cotensor A X.val
  map X Y := (cotensorMap A X.val Y.val).right
  map_id X := by
    change (PointedSimplicialSet.forgetUnit ≫ (identity A X.val).right) ≫
      (cotensorMap A X.val X.val).right = _
    rw [Category.assoc, ← Under.comp_right, identity_cotensorMap,
      RawSpectrumMapping.pointedIdentity_underlying]
    rfl
  map_comp X Y Z := by
    change (PointedSimplicialSet.productToSmash _ _ ≫
      (composition A X.val Y.val Z.val).right) ≫ (cotensorMap A X.val Z.val).right = _
    rw [Category.assoc, ← Under.comp_right, composition_cotensorMap, Under.comp_right,
      ← Category.assoc, ← PointedSimplicialSet.productToSmash_naturality,
      Category.assoc, RawSpectrumMapping.productToSmash_pointedComposition]
    rfl

end OmegaSpectrum.CotensorCompatible
end SerrePositivity.KST.Spectra
