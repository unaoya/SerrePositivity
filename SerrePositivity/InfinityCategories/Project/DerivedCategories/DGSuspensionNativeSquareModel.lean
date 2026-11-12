module
public import SerrePositivity.KST.NonConnective.DGSuspensionNativeSquareFamily
public import SerrePositivity.KST.NonConnective.DGSuspensionEnrichedAction

/-!
概要：D-8 e の全四角形族と厳密豊穣懸垂作用の接続を型として固定する。
方針：元の選択された四角形全体、元の入力作用、coherentNerveMap の供給路を保持する。
規約：未供給の中間型。実評価 Morita・元の P の全 native Hom 自然性はこの型に含まない。
使われ方：K-B3 へ先行公開する全四角形・懸垂成分の型。D-8 e 全仕様の完成とは数えない。
-/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.KST.SConstruction SerrePositivity.KST.NonConnective
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
variable (R : Type u) [CommRing R] {κ : Cardinal.{u}}
  (s : DGSuspensionStageProvider.{u, v} R κ)

/-- 同じ実四角形の全族と、指定された厳密豊穣供給路。存在は未証明。 -/
structure DGSuspensionNativeSquareModel where
  /-- 元の平坦懸垂と元の各厳密 dg 射を保つ全作用。 -/
  action : DGSuspensionNativeActionInput R s
  /-- 採用された厳密 SSet 豊穣供給路そのもの。 -/
  enriched : EnrichedFunctor SSet.{max (u + 1) v}
    (PerfDGInput.{u, max (u + 1) v} R) (PerfDGInput.{u, max (u + 1) v} R)
  /-- 豊穣関手の対象は同じ元の実平坦懸垂。 -/
  enriched_obj : ∀ A, enriched.obj A = dgKappaSuspensionKInput R A (s A).cone
  /-- 全単体上で同じ coherent nerve 射である。 -/
  enriched_map : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap enriched = action.map
  /-- 同じ実核・cone・零角・懸垂を全 native 入力で動かす全族。 -/
  square : ((Δ[1] ⊗ Δ[1]) ⊗ dgKInputInfinity.{u, max (u + 1) v} R) ⟶
    dgKInputInfinity.{u, max (u + 1) v} R
  /-- 各入力では四辺だけでなく、元の選んだ四角形全体と厳密一致。 -/
  square_at : ∀ A : PerfDGInput.{u, max (u + 1) v} R,
    dgSuspensionNativeSquareAt R square A = dgKappaResolvedConnectiveSquare R A (s A).cone
  /-- 懸垂角は全 native 入力で同じ厳密豊穣懸垂作用を回収する。 -/
  suspension : dgSuspensionNativeSquareCornerFamily R square 1 1 = action.map

variable (m : DGSuspensionNativeSquareModel R s)

theorem DGSuspensionNativeSquareModel.suspension_enriched :
    dgSuspensionNativeSquareCornerFamily R m.square 1 1 = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap m.enriched :=
  m.suspension.trans m.enriched_map.symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
