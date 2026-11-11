module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.FibrationFiberHomotopyComparison

/-!
概要：頂点 fiber の部分型模型と長完全列の引き戻し模型の厳密な同型。
方針：両方の持ち上げの普遍性を包含と固定条件に適用する。
規約：全空間と底の Kan 性や fibration 性は不要。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、既存の全次数比較を実際の導来 fiber の射へ戻す。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open SerrePositivity.KST.Spectra
open scoped _root_.Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
noncomputable section

/-- 概要：部分型の頂点 fiber と終対象からの引き戻しの fiber は厳密に同型。
方針：互いの包含を同じ固定条件で持ち上げる。
規約：同じ射 p と同じ頂点 b を使う。
使われ方：長完全列の fiber 比較の同値性を導来 fiber の部分型模型へ移す。 -/
def vertexFiberKanFiberIso {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p b where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift p b (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp p b)
  inv := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p b (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p b) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_comp p b)
  hom_inv_id := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p b
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift_ι, Category.id_comp]
  inv_hom_id := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_hom_ext p b
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, Category.id_comp]

/-- 概要：fiber 模型の同型の順射は全空間への包含と可換。
方針：引き戻しへの持ち上げの射影を計算する。
規約：全空間の射の厳密な等式。
使われ方：fiber 間の実際の比較射の座標の追跡。 -/
lemma vertexFiberKanFiberIso_hom_ι {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    (vertexFiberKanFiberIso p b).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p b = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift_ι p b (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp p b)

/-- 概要：fiber 模型の同型の逆射は全空間への包含と可換。
方針：部分型の fiber への持ち上げの包含を計算する。
規約：固定条件の証明の選択に依存しない。
使われ方：引き戻し模型から部分型模型へ比較射を戻す。 -/
lemma vertexFiberKanFiberIso_inv_ι {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    (vertexFiberKanFiberIso p b).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p b :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι p b (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p b) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_comp p b)

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
