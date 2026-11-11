module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanPointHomNaturality

/-!
概要：成分ごとに Kan な単体集合値図式を Kan 対象値の通常の図式として束ねる。
方針：元の対象・構造射・自然変換をそのまま使う。
規約：図式全体の strictification を主張するものではない。
使われ方：filtered な引き戻し模型を既存の SpaceInfinity の図式に渡す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {I : Type u} [SmallCategory I]

/-- 概要：成分が Kan な通常の図式を対象の Kan 性で束ねる。
方針：元の関手の構造射と関手則を使う。
規約：忘却後は元の関手と厳密に同じ。使われ方：native な極限・余極限模型。 -/
def kanDiagramOfSSet (F : I ⥤ SSet.{u}) [∀ i, KanComplex (F.obj i)] : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} where
  obj i := ⟨F.obj i, inferInstance⟩
  map f := F.map f
  map_id := F.map_id
  map_comp := F.map_comp

/-- 概要：束ねた Kan 図式の忘却は元の図式。
方針：対象・構造射の定義を使う。
規約：自然同型ではなく関手の等式。使われ方：元の colimit の同定。 -/
lemma kanDiagramOfSSet_forget (F : I ⥤ SSet.{u}) [∀ i, KanComplex (F.obj i)] :
    kanDiagramOfSSet F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget = F := rfl

/-- 概要：元の通常の自然変換を Kan 図式の自然変換として束ねる。
方針：元の全成分と自然性を使う。
規約：成分ごとの逆の選択は不要。使われ方：余極限後の cospan の比較。 -/
def kanDiagramOfSSetMap {F G : I ⥤ SSet.{u}}
    [∀ i, KanComplex (F.obj i)] [∀ i, KanComplex (G.obj i)] (η : F ⟶ G) :
    kanDiagramOfSSet F ⟶ kanDiagramOfSSet G where
  app i := η.app i
  naturality _ _ f := η.naturality f

end SerrePositivity.InfinityCategories.Project.FilteredExchange
