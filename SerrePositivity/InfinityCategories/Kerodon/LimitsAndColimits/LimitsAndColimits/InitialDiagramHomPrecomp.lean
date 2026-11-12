module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialDiagramHomFamily

/-!
概要：初期 Hom 族のパラメータ前合成の厳密な自然性。
方針：fiber 包含後に同じ全余錐族の前合成を比較する。
規約：図式や始点を変更しない。使われ方：普遍前置の始点と元の HL・HR の入力の照合。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 初期 Hom への制限は、全余錐族のパラメータ前合成と厳密に可換。 -/
lemma initialDiagramHomFamily_precomp {K E B T S : SSet.{u}}
    (q : E ⟶ B) (c : E _⦋0⦌) (t : K ⟶ E) (v : (Δ[0] : SSet.{u}) ⟶ K)
    (hv : v ≫ t = SSet.yonedaEquiv.symm c) (y : B _⦋0⦌)
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder t) (ha : (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection t) ≫ q = SSet.const y) (i : S ⟶ T) :
    i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialDiagramHomFamily q c t v hv y a ha =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialDiagramHomFamily q c t v hv y (i ≫ a)
        (by simpa only [Category.assoc, SSet.comp_const] using congrArg (i ≫ ·) ha) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm c) ≫ q) y
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialDiagramHomFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
