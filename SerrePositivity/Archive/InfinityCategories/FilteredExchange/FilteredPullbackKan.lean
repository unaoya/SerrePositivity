module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FilteredFiniteLimits
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FilteredKanFibrations
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanDiagramOfSSet
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FilteredKanColimitNative
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.SpacePullbacks
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks

/-!
概要：成分ごとに一脚が Kan fibration の引き戻し図式の filtered 比較を Kan 対象に束ねる。
方針：評価の引き戻し同型で各値の Kan 性を得て、filtered 引き戻し同型を使う。
規約：通常の strict 図式を扱う。任意の coherent 図式への拡張は別工程。
使われ方：𝒮 の filtered 余極限と引き戻しの native な比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {I : Type u} [SmallCategory I] {F G H : I ⥤ SSet.{u}}

/-- 概要：各段の一脚が fibration なら関手圏の引き戻しの各値は Kan。
方針：評価の標準同型で通常の Kan な引き戻しへ移す。
規約：Kan 性は第二入力の各値だけでも十分。使われ方：引き戻し図式の束縛。 -/
instance pullbackDiagram_kanComplex [∀ i, KanComplex (H.obj i)]
    (η : F ⟶ G) (θ : H ⟶ G) [∀ i, Fibration (η.app i)] (i : I) :
    KanComplex ((pullback η θ).obj i) := by
  have : KanComplex (pullback (η.app i) (θ.app i)) :=
    pullback_kanComplex_of_fibration (η.app i) (θ.app i)
  exact kanComplex_of_iso (pullbackObjIso η θ i).symm

variable [IsFiltered I] [∀ i, KanComplex (F.obj i)] [∀ i, KanComplex (G.obj i)]
  [∀ i, KanComplex (H.obj i)] (η : F ⟶ G) (θ : H ⟶ G) [∀ i, Fibration (η.app i)]

/-- 概要：元の二つの図式の余極限間の cospan の左脚。
方針：通常の colimit の誘導射を Kan 対象間の射として読む。
規約：台の射は colim.map η。使われ方：余極限後の native な引き戻し。 -/
def filteredKanLeftMap : filteredKanColimitObject (kanDiagramOfSSet F) ⟶
    filteredKanColimitObject (kanDiagramOfSSet G) := colim.map η

/-- 概要：元の二つの図式の余極限間の cospan の右脚。
方針：通常の colimit の誘導射を Kan 対象間の射として読む。
規約：台の射は colim.map θ。使われ方：余極限後の native な引き戻し。 -/
def filteredKanRightMap : filteredKanColimitObject (kanDiagramOfSSet H) ⟶
    filteredKanColimitObject (kanDiagramOfSSet G) := colim.map θ

/-- 概要：余極限後も cospan の左脚は Kan fibration。
方針：元の各段の相対ホーンの充填性の filtered 保存を使う。
規約：右脚の fibration 性は不要。使われ方：N の native な引き戻しへの入力。 -/
instance filteredKanLeftMap_fibration : Fibration
    (show (filteredKanColimitObject (kanDiagramOfSSet F)).obj ⟶
      (filteredKanColimitObject (kanDiagramOfSSet G)).obj from filteredKanLeftMap η) := by
  change Fibration (colim.map η)
  infer_instance

/-- 概要：引き戻し図式の余極限と余極限の引き戻しの比較を Kan 対象の同型にする。
方針：有限極限保存の標準同型の両射をそのまま使う。
規約：標的は N の native な引き戻し錐の頂点。使われ方：𝒮 の可逆な比較辺。 -/
def filteredKanPullbackColimitIso :
    filteredKanColimitObject (kanDiagramOfSSet (pullback η θ)) ≅
      (kanPullbackCone (filteredKanLeftMap η) (filteredKanRightMap θ)).pt where
  hom := (filteredPullbackIso η θ).hom
  inv := (filteredPullbackIso η θ).inv
  hom_inv_id := (filteredPullbackIso η θ).hom_inv_id
  inv_hom_id := (filteredPullbackIso η θ).inv_hom_id

end SerrePositivity.InfinityCategories.F2
