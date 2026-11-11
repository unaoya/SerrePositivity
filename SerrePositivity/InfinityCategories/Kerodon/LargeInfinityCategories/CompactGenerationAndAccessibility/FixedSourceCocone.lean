module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.RelativeComponentFactorization

/-!
概要：固定入力図式を伴う全余錐を、同じ入力図式の coslice 内へ戻す。
方針：既存の反復 coslice 同型の逆を適用し、元の右制限を計算する。
規約：同じ全余錐を使い、入力図式を選び直さない。
使われ方：固定小図式を保持する相対交互塔の一段追加。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility


private lemma iso_inv_hom_vertex {X Y : SSet.{u}} (e : X ≅ Y) (y : Y _⦋0⦌) :
    e.hom.app (Opposite.op ⦋0⦌) (e.inv.app (Opposite.op ⦋0⦌) y) = y :=
  ConcreteCategory.congr_hom (NatTrans.congr_app e.inv_hom_id (Opposite.op ⦋0⦌)) y

/-- 概要：展開した全図式の余錐を、固定入力図式の下の全余錐へ戻す。
方針：反復 coslice の既存同型の逆を使う。
規約：入力した全余錐を厳密に保持する。
使われ方：固定入力付きの一段延長。 -/
def fixedSourceCocone {K L C : SSet.{u}} {a : K ⟶ C}
    (R : L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry R)) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone R :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.iteratedSliceUnderIso R).inv.app (Opposite.op ⦋0⦌) d

/-- 概要：固定入力付き余錐の底は元の全余錐の右制限。
方針：既存の反復同型と右制限の可換性で、逆同型を相殺する。
規約：頂点だけでなく全余錐の等式。
使われ方：元の成分表示との全単体整合。 -/
lemma fixedSourceCocone_projection {K L C : SSet.{u}} {a : K ⟶ C}
    (R : L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry R)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a) (fixedSourceCocone R d)).val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K L) (𝟙 Δ[0]) ≫ d.val := by
  have hv : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp R (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a)).app (Opposite.op ⦋0⦌)
      (fixedSourceCocone R d) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.uncurriedSourceRightRestriction R).app (Opposite.op ⦋0⦌) d := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.iteratedSliceUnderIso_sourceRightRestriction R]
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.uncurriedSourceRightRestriction R).app _
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.iteratedSliceUnderIso R).hom.app _ ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.iteratedSliceUnderIso R).inv.app _ d)) = _
    exact congrArg
      (fun z : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry R)) _⦋0⦌ ↦
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.uncurriedSourceRightRestriction R).app (Opposite.op ⦋0⦌) z)
      (iso_inv_hom_vertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.iteratedSliceUnderIso R) d)
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp R (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a)).app _ (fixedSourceCocone R d)).val = _
  rw [hv]
  change ((eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection R))).hom.app
    (Opposite.op ⦋0⦌) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry R) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K L)).app
      (Opposite.op ⦋0⦌) d)).val = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.sliceUnder_eqToIso_val (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection R)]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
