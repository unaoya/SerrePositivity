module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialEdgeFamilyRetraction

/-!
概要：初期 Hom の相対辺比較の底を、元の底の切断比較の同じ円柱へ同定する。
方針：固定終点の包含後に同じ raw な始点制限を照合する。
規約：底の代表を選び直さない。使われ方：付加辺面と native な前合成比較の照合。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
noncomputable section
variable {E B T : SSet.{u}} [Quasicategory B] (q : E ⟶ B) [InnerFibration q]
  (c : E _⦋0⦌) (e : (Δ[1] : SSet.{u}) ⟶ E)
  (he : stdSimplex.δ (1 : Fin 2) ≫ e = SSet.yonedaEquiv.symm c)
  (y : B _⦋0⦌) (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder e)
  (ha : (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection e) ≫ q = SSet.const y)
local notation "hs" => Eq.trans (Eq.symm (Category.assoc (stdSimplex.δ (1 : Fin 2)) e q))
  (congrArg (· ≫ q) he)
local notation "I" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialEdgeFamilyRetraction q c e he y a ha
local notation "F" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeFamilyBase e q a y ha

/-- 比較の底は、元の底の全辺族の同じ切断比較を始点へ制限した円柱である。 -/
lemma initialEdgeFamilyRetraction_baseCylinder :
    (I).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q c y =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFamilyPrecompositionCylinder (e ≫ q) y F
        (SSet.yonedaEquiv.symm c ≫ q) (stdSimplex.δ (0 : Fin 2) ≫ (e ≫ q))
        hs rfl).h := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm c ≫ q)) y
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialEdgeFamilyRetraction_base,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFamilyPrecompositionCylinder_projection]
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι]

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
