module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentOppositeMap

/-!
概要：豊穣関手による coherent nerve の後合成と反対の標準射の自然性。
方針：各 simplex の豊穣関手へ後合成し、合成の結合則で添字と反対の比較を計算する。
規約：ここでは二つの対象の宇宙を同じ v とし、Hom の宇宙は u とする。
使われ方：Kerodon §4.6.7（Tag 01LA）、HTT 4.2.4.1 の係数の反対を豊穣関手と整合させる準備。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：単体的豊穣関手は coherent nerve の単体集合の射を誘導する。
方針：全ての coherent simplex の豊穣関手へ後合成する。
規約：C と D の対象の宇宙を v に揃える。
使われ方：Kerodon §4.6.7（Tag 01LA） の反対の標準比較の豊穣関手への自然性。 -/
def coherentNervePost {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D] (F : EnrichedFunctor SSet C D) :
    SimplicialNerve C ⟶ SimplicialNerve D where
  app _ := ↾fun G ↦ G.comp SSet F
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro G
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedFunctor_comp_assoc _ G F

/-- 概要：coherent simplex の反対を取る操作は豊穣関手の後合成と可換。
方針：反対の合成則と豊穣関手の合成の結合則を使う。
規約：単体の次数は任意。
使われ方：Kerodon §4.6.7（Tag 01LA） の反対の標準射の後合成への自然性。 -/
lemma coherentOppositeSimplex_post {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D] (F : EnrichedFunctor SSet C D)
    {n : ℕ} (G : (SimplicialNerve C) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentOppositeSimplex (G.comp SSet F) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentOppositeSimplex G).comp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedFunctorOp F) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentOppositeSimplex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedFunctorOp_comp,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedFunctor_comp_assoc]
  rfl

/-- 概要：coherent nerve の反対の標準射は豊穣関手に自然。
方針：各次数で coherent simplex の後合成と反対の可換性を使う。
規約：反対の豊穣関手の Hom は元の Hom を逆順に評価する。
使われ方：Kerodon §4.6.7（Tag 01LA） の Hom と係数図式の反対の自然な比較。 -/
lemma coherentNerveOppositeMap_post {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D] (F : EnrichedFunctor SSet C D) :
    SSet.opFunctor.map (coherentNervePost F) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveOppositeMap D =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveOppositeMap C ≫ coherentNervePost (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedFunctorOp F) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro G
  exact coherentOppositeSimplex_post F (SSet.opObjEquiv G)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
