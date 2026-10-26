module

public import SerrePositivity.KST.Spectra.AdjointLoopRelativeCompatibleEnrichment
public import SerrePositivity.KST.Spectra.SpectrumCotensorCompatibleFunctors

/-!
概要：相対 BF 左因子と可換な組から元の対象・置換対象への全 Hom 関手。
方針：二つの実射影を単体的豊穣関手へ束ねる。
規約：nativeLoop への比較をこの段階では主張しない。
使われ方：補助単位の相対 BF 比較を全高次単体へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance relativeFunctorsSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 概要：元の BF 対象と元の射への射影は、実際の単体的豊穣関手。
方針：二射影の厳密な単位・合成保存を基礎単体集合へ写す。
規約：選択した持ち上げに関手法則を仮定しない。
使われ方：指定左因子を保つ全図式比較。 -/
def originalEnriched :
    EnrichedFunctor SSet.{u} Object OmegaSpectrum.{u} where
  obj X := X.val
  map X Y := (originalMap X.val Y.val).right
  map_id X := by
    change (PointedSimplicialSet.forgetUnit ≫ (compatibleIdentity X.val).right) ≫
      (originalMap X.val X.val).right = _
    rw [Category.assoc, ← Under.comp_right, compatibleIdentity_originalMap,
      RawSpectrumMapping.pointedIdentity_underlying]
    rfl
  map_comp X Y Z := by
    change (PointedSimplicialSet.productToSmash _ _ ≫
      (compatibleComposition X.val Y.val Z.val).right) ≫ (originalMap X.val Z.val).right = _
    rw [Category.assoc, ← Under.comp_right, compatibleComposition_originalMap, Under.comp_right,
      ← Category.assoc, ← PointedSimplicialSet.productToSmash_naturality,
      Category.assoc, RawSpectrumMapping.productToSmash_pointedComposition]
    rfl

/-- 概要：相対 BF 置換 の対象と整合する射への射影も、実際の単体的豊穣関手。
方針：二射影の厳密な単位・合成保存を基礎単体集合へ写す。
規約：選択した持ち上げに関手法則を仮定しない。
使われ方：指定左因子を保つ全図式比較。 -/
def replacedEnriched :
    EnrichedFunctor SSet.{u} Object OmegaSpectrum.{u} where
  obj X := middle X.val
  map X Y := (replacedMap X.val Y.val).right
  map_id X := by
    change (PointedSimplicialSet.forgetUnit ≫ (compatibleIdentity X.val).right) ≫
      (replacedMap X.val X.val).right = _
    rw [Category.assoc, ← Under.comp_right, compatibleIdentity_replacedMap,
      RawSpectrumMapping.pointedIdentity_underlying]
    rfl
  map_comp X Y Z := by
    change (PointedSimplicialSet.productToSmash _ _ ≫
      (compatibleComposition X.val Y.val Z.val).right) ≫ (replacedMap X.val Z.val).right = _
    rw [Category.assoc, ← Under.comp_right, compatibleComposition_replacedMap, Under.comp_right,
      ← Category.assoc, ← PointedSimplicialSet.productToSmash_naturality,
      Category.assoc, RawSpectrumMapping.productToSmash_pointedComposition]
    rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
