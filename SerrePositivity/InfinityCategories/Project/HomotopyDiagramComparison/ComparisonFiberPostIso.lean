module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.ComparisonFiberPost

/-!
概要：標的の厳密な同型による導来 fiber の固定点を保持した比較。
方針：実際の後合成の fiber 射と同型の逆による固定点の厳密な等式を組み合わせる。
規約：同値の逆の新しい選択はせず、指定した同型の逆射を使う。
使われ方：HTT 4.2.4.1、反転の極限保存同型を介する元の比較との照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 概要：標的を同型で移すと任意の固定点の導来 fiber は指定した逆射の像の fiber と同値。
方針：逆の点の後合成の比較と、同型の逆の合成が恒等射である式による移送を合成する。
規約：元の射の fibration 性は不要。固定点は同型の逆射で厳密に回収する。
使われ方：反転の極限保存同型による比較射の導来 fiber の移送。 -/
def comparisonFiberPostIsoEquivalence {E B D : SSet.{u}}
    [KanComplex E] [KanComplex B] [KanComplex D] (p : E ⟶ B) (e : B ≅ D) (b : D _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber p (e.inv.app _ b)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (p ≫ e.hom) b) := by
  have hb : e.hom.app (Opposite.op ⦋0⦌) (e.inv.app _ b) = b :=
    ConcreteCategory.congr_hom (NatTrans.congr_app e.inv_hom_id _) b
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.comparisonFiberPost_homotopyEquivalence p e.hom
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.homotopyEquivalence_of_isIso e.hom) (e.inv.app _ b)).isQCatEquivalence.choose.trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (eqToIso (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (p ≫ e.hom)) hb)))

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
