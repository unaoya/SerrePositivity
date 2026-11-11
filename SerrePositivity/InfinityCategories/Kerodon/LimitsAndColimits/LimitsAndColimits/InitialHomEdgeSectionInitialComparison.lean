module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialHomEdgeSectionComparison

/-!
概要：保持した同じ全辺族の終点・底固定比較を、元の中間持ち上げへの初期 Hom 円柱へ移す。
方針：比較円柱を同じ初期頂点へ制限し、固定終点の fiber に戻す。
規約：終点は既存データの lift そのもの。使われ方：前置写像と元の HL・HR の類の照合。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
noncomputable section
variable {E B T : SSet.{u}} [Quasicategory B] (q : E ⟶ B) [InnerFibration q]
  (c : E _⦋0⦌) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex c) (e : (Δ[1] : SSet.{u}) ⟶ E)
  (he : stdSimplex.δ (1 : Fin 2) ≫ e = SSet.yonedaEquiv.symm c) (y : B _⦋0⦌)
  (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (stdSimplex.δ (0 : Fin 2) ≫ e))
  (ha : (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ e)) ≫ q = SSet.const y)
  (b : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (e ≫ q))
  (h : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (stdSimplex.δ (0 : Fin 2) ≫ e) q =
    b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict (e ≫ q) (stdSimplex.δ (0 : Fin 2)))
  (hb : b = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (stdSimplex.δ (0 : Fin 2) ≫ e) q ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSection (e ≫ q))
local notation "D" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialHomEdgeCylinder q c hc e he y a ha b h
local notation "H" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialHomEdgeSectionComparison q c hc e he y a ha b h hb
local notation "P" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction e (stdSimplex.δ (1 : Fin 2)) he
local notation "v" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift q y
  (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ e)) ha

include ha in
/-- 普遍相対切断の像も、同じ底の終点 y 上に留まる。 -/
lemma initialHomEdgeSectionInput_fixed :
    ((a ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeCosliceSection e q) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection e) ≫ q = SSet.const y := by
  rw [Category.assoc a (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeCosliceSection e q) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection e),
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeCosliceSection_projection]
  exact ha

/-- 同じ全辺族の比較中も、底の終点は円柱の全時刻で y に固定される。 -/
lemma initialHomEdgeSectionComparison_fixed :
    ((H).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection e) ≫ q = SSet.const y := by
  calc
    _ = ((H).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict e (stdSimplex.δ (0 : Fin 2))) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ e) ≫ q) := by
      simpa only [Category.assoc] using
        (congrArg (fun z ↦ ((H).h ≫ z) ≫ q)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_projection e (stdSimplex.δ (0 : Fin 2))).symm)
    _ = (fst T Δ[1] ≫ a) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ e) ≫ q) :=
      congrArg (· ≫ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialHomEdgeSectionComparison_target q c hc e he y a ha b h hb)
    _ = fst T Δ[1] ≫ ((a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ e)) ≫ q) := by
      simp only [Category.assoc]
    _ = _ := by rw [ha, SSet.comp_const]

/-- 全辺族の同じ比較を初期 Hom に制限し、元の lift を終点として保持する。 -/
def initialHomEdgeSectionInitialComparison : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialDiagramHomFamily q c e (stdSimplex.δ (1 : Fin 2)) he y
      (a ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeCosliceSection e q)
      (initialHomEdgeSectionInput_fixed q e y a ha)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialHomEdgeCylinder.lift D) where
  h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm c) ≫ q) y ((H).h ≫ P)
    (by
      rw [← Category.assoc ((H).h ≫ P), Category.assoc (H).h P,
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction_projection]
      exact initialHomEdgeSectionComparison_fixed q c hc e he y a ha b h hb)
  h₀ := by
    change SSet.ι₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ y ((H).h ≫ P) _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialDiagramHomFamily q c e (stdSimplex.δ (1 : Fin 2)) he y
        (a ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeCosliceSection e q) (initialHomEdgeSectionInput_fixed q e y a ha)
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, ← Category.assoc, SSet.Homotopy.h₀,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialDiagramHomFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
  h₁ := by
    change SSet.ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ y ((H).h ≫ P) _ = (D).lift
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, ← Category.assoc, SSet.Homotopy.h₁]
    exact (D).lift_ι.symm
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property
local notation "K" => initialHomEdgeSectionInitialComparison q c hc e he y a ha b h hb

/-- 包含後は、元の同じ全辺族の比較円柱の初期制限そのもの。 -/
lemma initialHomEdgeSectionInitialComparison_ι :
    (K).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm c) ≫ q) y = (H).h ≫ P := by
  rw [initialHomEdgeSectionInitialComparison, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]

/-- 初期 Hom 比較の評価は、元の終点側の全族を全時刻で厳密に保持する。 -/
lemma initialHomEdgeSectionInitialComparison_evaluation :
    (K).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation q c y = fst T Δ[1] ≫ v := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext q y
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι, ← Category.assoc,
    initialHomEdgeSectionInitialComparison_ι, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction_projection, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
  have hH := congrArg (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ e))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialHomEdgeSectionComparison_target q c hc e he y a ha b h hb)
  simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_projection] using hH

/-- 初期 Hom 比較の底も、元の lift の底の全族を全時刻で固定する。 -/
lemma initialHomEdgeSectionInitialComparison_base :
    (K).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q c y =
      fst T Δ[1] ≫ (D).lift ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q c y := by
  let R := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction (e ≫ q) (stdSimplex.δ (1 : Fin 2))
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ q) he))
  have hp : (K).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q c y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm c ≫ q)) y =
      ((H).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp e q) ≫ R := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι,
      ← Category.assoc, initialHomEdgeSectionInitialComparison_ι]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction_postcomp_family e (stdSimplex.δ (1 : Fin 2))
      (SSet.yonedaEquiv.symm c) he q (H).h
  have hd : (D).lift ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q c y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm c ≫ q)) y = b ≫ R := by
    rw [← Category.assoc (D).lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q c y)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm c ≫ q)) y),
      (D).projection, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialEdgeBaseSource, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm c ≫ q)) y
  exact (Category.assoc _ _ _).trans
    (hp.trans ((congrArg (· ≫ R)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialHomEdgeSectionComparison_base q c hc e he y a ha b h hb)).trans
        ((Category.assoc _ _ _).trans ((congrArg (fst T Δ[1] ≫ ·) hd.symm).trans
          (Category.assoc _ _ _).symm))))

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
