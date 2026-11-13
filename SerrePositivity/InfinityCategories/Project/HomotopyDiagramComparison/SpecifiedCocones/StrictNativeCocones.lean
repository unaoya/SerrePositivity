module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.StrictOppositeDiagram

/-!
概要：通常の余錐を元の標準図式上の native な余錐とし、その余極限性を反対の極限性へ移す。
方針：双対化した図式の全単体の等式で正規化し、値・頂点・余極限性を保持する。
規約：固定図式は既存の strictCoherentDiagram F そのもの。
使われ方：HTT 4.2.4.1、余積・homotopy 押し出し・逐次 homotopy 余極限の公開の界面。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 概要：通常の余錐は元の標準の coherent 図式上の native な余錐を定める。
方針：双対化した余錐を図式の厳密な等式で正規化する。
規約：Kan 性や余極限性は定義に要求しない。
使われ方：元の通常の図式に対する実際の ∞ 余極限余錐。 -/
def strictNativeCocone {F : I ⥤ C} (c : Cocone F) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictCoherentCoconeDiagram_eq F) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCocone c)

/-- 概要：標準の図式へ正規化しても余錐の join からの射は変更しない。
方針：固定図式の等式による移送の値の式を使う。
規約：双対化した実際の余錐と同じ射である。
使われ方：元の余錐の各脚との厳密な照合。 -/
lemma strictNativeCocone_val {F : I ⥤ C} (c : Cocone F) :
    (strictNativeCocone c).val = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCocone c).val :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_val _ _

/-- 概要：標準の coherent 図式上の余錐の頂点は元の通常の余錐の頂点。
方針：固定図式の移送が頂点を保つことと双対化した余錐の頂点の式を合成する。
規約：元の対象 c.pt の標準の coherent nerve の頂点。
使われ方：構成した ∞ 余極限対象と元の strict な対象の照合。 -/
lemma strictNativeCocone_vertex {F : I ⥤ C} (c : Cocone F) :
    (strictNativeCocone c).vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex c.pt := by
  rw [strictNativeCocone, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCocone_vertex]

/-- 概要：元の標準図式上の通常の余錐が ∞ 余極限であることは反対の錐の ∞ 極限性と同値。
方針：図式の正規化の不変性を、双対化した余錐の極限判定へ接続する。
規約：通常の余錐 c と添字 I は任意。局所 Kan 性はこの形式的な双対化には不要。
使われ方：HTT 4.2.4.1、極限側の定理を元の図式の native な余極限へ移す。 -/
lemma strictNativeCocone_isColimit_iff {F : I ⥤ C} (c : Cocone F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (strictNativeCocone c) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c.op) :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_isColimit_iff _ _).symm.trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCocone_isColimit_iff c)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
