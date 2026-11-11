module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinConeCoordinates

/-!
概要：余錐間の元の prism から全図式の余錐への形状の射を構成する。
方針：join と直積の座標を保ち、元の両端と頂点の射を厳密に照合する。
規約：底 K は任意の単体集合。使われ方：HTT 5.5.4.5(2) の余極限閉性。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 全図式の右錐を、元の余錐間の prism へ写す標準射。 -/
def colimitPrismTotalMap (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join ((Δ[1] : SSet.{u}) ⊗ K) Δ[0] ⟶ (Δ[1] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K Δ[0] :=
  lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (fst (Δ[1] : SSet.{u}) K) (𝟙 (Δ[0] : SSet.{u})) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinConeTime)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (snd (Δ[1] : SSet.{u}) K) (𝟙 (Δ[0] : SSet.{u})))

/-- 全図式の右錐の底は、元の prism の底図式の包含を厳密に回収する。 -/
lemma colimitPrismTotalMap_inl (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl ((Δ[1] : SSet.{u}) ⊗ K) Δ[0] ≫ colimitPrismTotalMap K =
      (Δ[1] : SSet.{u}) ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0] := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [colimitPrismTotalMap, Category.assoc, lift_fst, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinConeTime_inl, Category.comp_id,
      whiskerLeft_fst]
  · rw [colimitPrismTotalMap, Category.assoc, lift_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, whiskerLeft_snd]

/-- 全図式の右錐の新頂点は、元の prism の終点余錐の頂点となる。 -/
lemma colimitPrismTotalMap_inr (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr ((Δ[1] : SSet.{u}) ⊗ K) Δ[0] ≫ colimitPrismTotalMap K =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K Δ[0] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K Δ[0]) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [colimitPrismTotalMap, Category.assoc, lift_fst, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinConeTime_inr,
      Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, lift_fst, SSet.comp_const]
  · rw [colimitPrismTotalMap, Category.assoc, lift_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp,
      Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, lift_snd, Category.comp_id]

/-- 全図式の右錐を終点面へ制限すると、元の終点余錐の包含となる。 -/
lemma colimitPrismTotalMap_target (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) (𝟙 (Δ[0] : SSet.{u})) ≫ colimitPrismTotalMap K =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K Δ[0]) := by
  apply CartesianMonoidalCategory.hom_ext
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCone_hom_ext_stdSimplex
    · simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap]
      rw [Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K), colimitPrismTotalMap_inl,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality]
    · simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp,
        colimitPrismTotalMap_inr]
  · rw [colimitPrismTotalMap, Category.assoc, lift_snd, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp]
    simp only [Category.comp_id, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, lift_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_id, lift_snd]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
