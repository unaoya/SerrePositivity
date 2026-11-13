module

public import SerrePositivity.KST.Spectra.AdjointLoopRelativeCompatibleFunctors
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.EnrichedParameterCylinderRestriction

/-!
概要：相対 BF 左因子を二つの全 Hom 関手の間の厳密な豊穣自然変換へ束ねる。
方針：指定左因子の全正方形条件を使い、smash 忘却と単位制限を適用する。
規約：点ごとの π 同型から自然性を推論しない。
使われ方：同じ実左因子を成分とする全図式比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance : EnrichedCategory PointedSimplicialSet.{u} OmegaSpectrum.{u} :=
  pointedEnrichment

/-- 概要：元の BF 対象への射影は点つき豊穣関手。
方針：元の射影の単位・合成保存を使う。
規約：指定した元の全 Hom を保持する。
使われ方：左因子の豊穣自然変換の始域。 -/
def originalPointedEnriched :
    EnrichedFunctor PointedSimplicialSet.{u} Object OmegaSpectrum.{u} where
  obj X := X.val
  map X Y := originalMap X.val Y.val
  map_id X := compatibleIdentity_originalMap X.val
  map_comp X Y Z := compatibleComposition_originalMap X.val Y.val Z.val

/-- 概要：相対 BF 置換対象への射影も点つき豊穣関手。
方針：置換射影の単位・合成保存を使う。
規約：選択した置換を元の圏上の通常関手としない。
使われ方：左因子の豊穣自然変換の終域。 -/
def replacedPointedEnriched :
    EnrichedFunctor PointedSimplicialSet.{u} Object OmegaSpectrum.{u} where
  obj X := middle X.val
  map X Y := replacedMap X.val Y.val
  map_id X := compatibleIdentity_replacedMap X.val
  map_comp X Y Z := compatibleComposition_replacedMap X.val Y.val Z.val

/-- 概要：同じ相対 BF 左因子は全 Hom 上で厳密に豊穣自然。
方針：実引き戻しの正方形条件を単位パラメータの条件へ移す。
規約：全パラメータの等式を実証する。
使われ方：coherent nerve の全図式比較の入力。 -/
def pointedGradedInclusion :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ PointedSimplicialSet.{u}))
      originalPointedEnriched replacedPointedEnriched where
  app X := inclusionPoint X.val
  naturality X Y :=
    ((compatible_condition_iff X.val Y.val _ _).mp (compatible_condition X.val Y.val)).symm

local instance relativeGradedSpectrumSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 概要：元の左因子の豊穣自然性を全直積パラメータへ移す。
方針：smash 商と豊穣合成の自然性で全正方形を写す。
規約：基点を忘れた後も同じ成分を保つ。
使われ方：単体的圏の全図式比較。 -/
def unpointedGradedInclusion :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ PointedSimplicialSet.{u}).right)
      originalEnriched replacedEnriched where
  app X := (inclusionPoint X.val).right
  naturality X Y := by
    let A := 𝟙_ PointedSimplicialSet.{u}
    let P := compatibleSpace X.val Y.val
    have h := congrArg (fun f ↦ PointedSimplicialSet.productToSmash A P ≫ f.right)
      (((compatible_condition_iff X.val Y.val _ _).mp (compatible_condition X.val Y.val)).symm)
    simp only [Under.comp_right] at h
    rw [← reassoc_of% (PointedSimplicialSet.productToSmash_braiding A P)] at h
    rw [← reassoc_of% (PointedSimplicialSet.productToSmash_naturality
      (originalMap X.val Y.val) (inclusionPoint Y.val))] at h
    rw [← reassoc_of% (PointedSimplicialSet.productToSmash_naturality
      (inclusionPoint X.val) (replacedMap X.val Y.val))] at h
    rw [RawSpectrumMapping.productToSmash_pointedComposition,
      RawSpectrumMapping.productToSmash_pointedComposition] at h
    exact h

/-- 概要：元の相対 BF 左因子を成分とする通常の単体的豊穣自然変換。
方針：点つき単位の非基点側へパラメータを制限する。
規約：元の左因子の頂点を変えない。
使われ方：点ごとの同値から全図式 FunctorIso を組む。 -/
def gradedInclusion :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) originalEnriched replacedEnriched :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.gradedRestriction PointedSimplicialSet.forgetUnit
    originalEnriched replacedEnriched unpointedGradedInclusion

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
