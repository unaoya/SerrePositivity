module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.RelativeEdgeCosliceSection
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialDiagramHomFamily
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialRestrictionBaseEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceEdgeFiberPrecomposition

/-!
概要：枝始点の初期 Hom 空間全体を、指定比較辺を含む全辺族へ延長する。
方針：終点側の包含を相対 coslice 切断へ入力し、底と終点を厳密に回収する。
規約：入力の初期 Hom の点を選び直さない。使われ方：実際の付加比較辺による前置。

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
variable {E B : SSet.{u}} [Quasicategory B] (q : E ⟶ B) [InnerFibration q]
  {c d : E _⦋0⦌} (e : E.Edge c d) (y : B _⦋0⦌)
local notation "t" => SSet.yonedaEquiv.symm (SSet.Edge.edge e)
local notation "ιd" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm d) ≫ q) y

omit [Quasicategory B] [InnerFibration q] in
/-- 比較辺の底の始点は、元の始点の底の点図式そのもの。 -/
lemma initialTotalEdgeBase_source :
    stdSimplex.δ (1 : Fin 2) ≫ (t ≫ q) = SSet.yonedaEquiv.symm c ≫ q :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ q) (SSet.Edge.δ_one_yonedaEquiv_symm e))

omit [Quasicategory B] [InnerFibration q] in
/-- 比較辺の底の終点も、元の終点の底の点図式そのもの。 -/
lemma initialTotalEdgeBase_target :
    stdSimplex.δ (0 : Fin 2) ≫ (t ≫ q) = SSet.yonedaEquiv.symm d ≫ q :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ q) (SSet.Edge.δ_zero_yonedaEquiv_symm e))

/-- 元の初期 Hom 空間全体を、その終点を保って比較辺全体の族へ延長する。 -/
def initialTotalEdgeFamily : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialTotal q d y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder t :=
  ιd ≫ eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.Edge.δ_zero_yonedaEquiv_symm e).symm) ≫
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeCosliceSection t q
local notation "F" => initialTotalEdgeFamily q e y

/-- 延長族を正規化して終点へ戻すと、入力した同じ初期 Hom の包含そのもの。 -/
lemma initialTotalEdgeFamily_target :
    F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction t (stdSimplex.δ (0 : Fin 2))
        (SSet.Edge.δ_zero_yonedaEquiv_symm e) = ιd := by
  simp only [initialTotalEdgeFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction, Category.assoc]
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeCosliceSection t q), _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeCosliceSection_target]
  simp only [Category.id_comp, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- 延長族の可変終点は、入力の初期 Hom 空間の可変終点そのもの。 -/
lemma initialTotalEdgeFamily_endpoint :
    F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection t = ιd ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm d) := by
  have h := congrArg (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm d))
    (initialTotalEdgeFamily_target q e y)
  simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction_projection] using h

/-- 延長族は、底の同じ終点 y 上に留まる。 -/
lemma initialTotalEdgeFamily_fixed : (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection t) ≫ q = SSet.const y := by
  rw [initialTotalEdgeFamily_endpoint, Category.assoc]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm d) ≫ q) y

omit [Quasicategory B] [InnerFibration q] in
/-- 終点表示の変更と底への射影は、同じ点図式の表示変更として可換。 -/
lemma initialTotalEdgeFamily_baseInput :
    (ιd ≫ eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.Edge.δ_zero_yonedaEquiv_symm e).symm)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (stdSimplex.δ (0 : Fin 2) ≫ t) q =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q d y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm d ≫ q)) y) ≫
          eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (initialTotalEdgeBase_target q e).symm) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_injective (stdSimplex.δ (0 : Fin 2) ≫ (t ≫ q))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_postcomp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceUnderUncurry_eqToHom (SSet.Edge.δ_zero_yonedaEquiv_symm e).symm,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceUnderUncurry_eqToHom (initialTotalEdgeBase_target q e).symm,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_postcomp]

/-- 延長族の底は、入力の射影と同じ指定した底の合成切断から作る族である。 -/
lemma initialTotalEdgeFamily_base : F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp t q =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q d y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm d ≫ q)) y) ≫
        eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (initialTotalEdgeBase_target q e).symm) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSection (t ≫ q) := by
  rw [initialTotalEdgeFamily, Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeCosliceSection_base]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSection (t ≫ q)) (initialTotalEdgeFamily_baseInput q e y))

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
