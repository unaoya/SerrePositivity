module

public import SerrePositivity.EInfinity.Hammock.WeakTwoOfSix

/-!
# 弱可縮な元の二対象間の実際の射

概要：両対象が弱可縮なら任意の元の射は弱ホモトピー同値となる。
方針：元の終射の一意性と二対三則を使う。
規約：モデル構造や始終域の Kan 性は要求しない。
使われ方：有限部分木の包含・葉の除去の同じ比較射。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory Limits SerrePositivity.InfinityCategories

lemma weak_of_contractible {A B : SSet.{u}} (f : A ⟶ B)
    (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible A) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence f := by
  have he : f ≫ terminal.from B = terminal.from A := terminal.hom_ext _ _
  have hfg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (f ≫ terminal.from B) := he.symm ▸ hA
  exact hB.cancel_right hfg

end SerrePositivity.EInfinity.Hammock
