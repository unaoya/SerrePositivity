module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.IntervalDiagramEvaluation
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FilteredIntervalPullback
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanIntervalPullbackNative
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FilteredPullbackKan

/-!
概要：任意の strict Kan cospan 図式の path 引き戻しの filtered 比較を Kan 対象に束ねる。
方針：各段の評価同型で Kan 性を得て、構成済みの二段の比較同型を使う。
規約：元の自然変換に fibration 性は不要。
使われ方：𝒮 の引き戻しと filtered 余極限の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {I : Type u} [SmallCategory I] {F G H : I ⥤ SSet.{u}}
  [∀ i, KanComplex (F.obj i)] [∀ i, KanComplex (G.obj i)] [∀ i, KanComplex (H.obj i)]

/-- 概要：任意の Kan 値 cospan の path 引き戻し図式は各段で Kan。
方針：成分の path 引き戻しとの評価同型を逆に使う。
規約：元の両射の相対充填性は不要。使われ方：図式の Kan 対象への束縛。 -/
instance intervalPullbackDiagram_kanComplex (η : F ⟶ G) (θ : H ⟶ G) (i : I) :
    KanComplex ((intervalPullbackDiagram η θ).obj i) :=
  kanComplex_of_iso (intervalPullbackObjIso η θ i).symm

/-- 概要：path 引き戻し図式を Kan 対象値の通常の図式にする。
方針：元の対象・構造射をそのまま束ねる。
規約：同じ添字 I と strict な構造射。使われ方：native な filtered 余極限。 -/
def intervalPullbackKanDiagram (η : F ⟶ G) (θ : H ⟶ G) : I ⥤ KanObject.{u} :=
  kanDiagramOfSSet (intervalPullbackDiagram η θ)

/-- 概要：各段の Kan 対象は元の二射の native な path 引き戻し対象に同型。
方針：二段の評価同型の両射を束ねる。
規約：台の比較は標準の intervalPullbackObjIso。使われ方：各段の模型の同定。 -/
def intervalPullbackDiagramKanObjIso (η : F ⟶ G) (θ : H ⟶ G) (i : I) :
    (intervalPullbackKanDiagram η θ).obj i ≅
      intervalPullbackKanObject ((kanDiagramOfSSetMap η).app i)
        ((kanDiagramOfSSetMap θ).app i) where
  hom := (intervalPullbackObjIso η θ i).hom
  inv := (intervalPullbackObjIso η θ i).inv
  hom_inv_id := (intervalPullbackObjIso η θ i).hom_inv_id
  inv_hom_id := (intervalPullbackObjIso η θ i).inv_hom_id

/-- 概要：path 引き戻し図式の余極限と元の余極限の二射の path 引き戻しの Kan 同型。
方針：二段の path 引き戻しの標準比較の両射を束ねる。
規約：fibration 仮定を追加しない。使われ方：元の cospan の native な極限との比較。 -/
def filteredIntervalPullbackKanIso [IsFiltered I] (η : F ⟶ G) (θ : H ⟶ G) :
    filteredKanColimitObject (intervalPullbackKanDiagram η θ) ≅
      intervalPullbackKanObject (filteredKanLeftMap η) (filteredKanRightMap θ) where
  hom := (intervalPullbackColimitIso η θ).hom
  inv := (intervalPullbackColimitIso η θ).inv
  hom_inv_id := (intervalPullbackColimitIso η θ).hom_inv_id
  inv_hom_id := (intervalPullbackColimitIso η θ).inv_hom_id

end SerrePositivity.InfinityCategories.F2
