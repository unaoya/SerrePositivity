module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorComposition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulCalculus

/-!
概要：Kan 標的の同値を通じて、前合成の実際のホモトピー同値性を検出する。
方針：前合成の自然性と内部 Hom の後合成同値で可換四角形を消去する。
規約：元の前合成の始域・終域の Kan 性は要求しない。
使われ方：元の値の持ち上げへの検査を pointed-space fiber への検査へ戻す。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 概要：同値な Kan 標的での前合成が同値なら元の標的での前合成も同値。
方針：自然性の正方形の二つの後合成同値を消去する。
規約：始域・終域は任意。使われ方：必要な fiber 標的への前合成同値。 -/
lemma pre_homotopyEquivalence_of_target_equivalence {A B Y Z : SSet.{u}}
    [KanComplex Y] [KanComplex Z] (f : A ⟶ B) (g : Y ⟶ Z) (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence g)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence ((pre f).app Z)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence ((pre f).app Y) := by
  have hA := (hg.postcompose A).isSimplicialHomotopyEquivalence
  have hB := (hg.postcompose B).isSimplicialHomotopyEquivalence
  apply hA.cancel_right
  rw [← (pre f).naturality g]
  exact hB.comp hf

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
