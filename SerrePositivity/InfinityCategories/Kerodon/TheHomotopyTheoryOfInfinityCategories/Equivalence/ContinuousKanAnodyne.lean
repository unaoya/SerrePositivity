module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.HornCellAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanSequence

/-!
概要：具体的な連続 Kan 関手への元の単位射は anodyne。
方針：各段のホーン付加を可算の超限合成に束ね、anodyne 性の閉性を使う。
規約：AsSmall に持ち上げた列の余極限を元の自然数圏へ制限して使う。
使われ方：連続 Kan 置換の単位の弱同値性と有限部分の収縮の移送。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：連続 Kan 関手の単位は点ごとにホーン付加の可算超限合成である。
方針：自然数の列の余極限に、各後続射の一段の anodyne 性を付ける。
規約：元の自然変換を変えずに表示する。
使われ方：単位全体の anodyne 性の判定。 -/
def continuousKanReplacementUnit_anodyneComposition :
    (anodyneExtensions.{u}.functorCategory SSet.{u}).TransfiniteCompositionOfShape ℕ
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.{u} := by
  let c := (colimit.cocone _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornCellSequence.{u}).whisker AsSmall.up
  refine
    { F := AsSmall.up ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornCellSequence.{u}
      isoBot := Iso.refl _
      incl := c.ι
      isColimit := (colimit.isColimit _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornCellSequence.{u}).whiskerEquivalence AsSmall.equiv
      fac := by rfl
      map_mem := ?_ }
  intro j _ X
  change anodyneExtensions
    (((Functor.ofSequence _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornCellStageMap).map (homOfLE (Nat.le_succ j))).app X)
  rw [Functor.ofSequence_map_homOfLE_succ]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.hornCellStepUnit_anodyne ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornCellStage j).obj X)

/-- 概要：連続 Kan 関手への元の単位射は全ての対象で anodyne。
方針：関手圏での可算超限合成に対する anodyne 性の閉性を適用する。
規約：X の Kan 性は仮定しない。
使われ方：任意の単体集合からの実際の Kan 置換の単位。 -/
lemma continuousKanReplacementUnit_anodyne (X : SSet.{u}) :
    anodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X) := by
  have h := (anodyneExtensions.{u}.functorCategory SSet.{u}).transfiniteCompositionsOfShape_le
    ℕ _ continuousKanReplacementUnit_anodyneComposition.mem
  exact h X

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
