module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NervePostcomposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity

/-!
概要：小さい単体的圏から Kan 複体への豊穣関手を、宇宙を保持して実現する。
方針：各 coherent 単体の豊穣関手へ後合成する。
規約：全次数の作用を定義し、頂点の値だけから自然性を推論しない。
使われ方：表現可能関手の coherent 比較の始域。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 小さい coherent nerve 上での Kan 値豊穣関手の実現。 -/
def smallKanRealization {D : Type u} [Category.{u} D] [SimplicialCategory D]
    (F : EnrichedFunctor SSet.{u} D _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialNerve D) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} where
  app _ := ↾fun s => s.down.comp SSet F
  naturality _ _ _ := rfl

/-- 実現の頂点は同じ豊穣関手の対象の coherent 頂点。 -/
lemma smallKanRealization_vertex {D : Type u} [Category.{u} D] [SimplicialCategory D]
    (F : EnrichedFunctor SSet.{u} D _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (y : D) :
    (smallKanRealization F).app (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex y)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (F.obj y) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object
    ((smallKanRealization F).app (Opposite.op ⦋0⦌)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex y)))).symm

/-- 豊穣関手による底変換は全単体で実現と可換。 -/
lemma smallKanRealization_precomp {C D : Type u} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D]
    (G : EnrichedFunctor SSet.{u} C D) (F : EnrichedFunctor SSet.{u} D _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap G) ≫ smallKanRealization F =
      smallKanRealization (G.comp SSet F) := rfl

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
