module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.DiscreteSpace

/-!
概要：離散埋め込みの全単体を同じ通常 nerve の coherent 表示へ同定する。
方針：零・一単体を正規化した既存の式を全次数で用いる。
規約：頂点だけの一致ではなく単体集合の射の等式。
使われ方：HTT 5.5.6.28、Kerodon §3.1（Tag 00SZ）、S8 の評価の自然性。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 離散埋め込みは同じ setsToKan の通常 nerve の coherent 表示。
HTT 5.5.6.28、Kerodon §3.1（Tag 00SZ）。全高次単体も保持する。 -/
lemma discreteSpaceInclusion_eq_coherent :
    discreteSpaceInclusion.{u} = nerveMap setsToKan ≫ nerveToCoherent KanObject := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  exact DiscreteSpaceModel.simplex_eq n.unop.len s

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
