module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialHomEdgeComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibrationInitialNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.PointCoslicePostIso

/-!
概要：底上の関手と実際の比較辺から、Hom 比較の自然性に入力する余錐の全パラメータ族を作る。
方針：既存の始点固定比較 span の写像を使い、辺の終点の表示に正規化する。
規約：像の始点の始対象性は不要。元の評価と底の固定終点を厳密に保持する。
使われ方：部分図式への余錐の制限と、部分余極限頂点の比較辺の高次の照合。

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
variable {E F B : SSet.{u}} (p : E ⟶ B) (q : F ⟶ B)
  (r : E ⟶ F) (hr : r ≫ q = p) (d : E _⦋0⦌) (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex d)
  {c : F _⦋0⦌} (e : F.Edge c (r.app (Opposite.op ⦋0⦌) d)) (y : B _⦋0⦌)

/-- 始対象からの族を底上の関手で写し、比較辺の終点側の coslice で表示する。 -/
def initialRestrictionEdgeFamily :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (stdSimplex.δ (0 : Fin 2) ≫ SSet.yonedaEquiv.symm e.edge) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialSection p d hd y ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialTotalMap p q r hr d (r.app (Opposite.op ⦋0⦌) d) rfl y ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection
      (SSet.yonedaEquiv.symm (r.app (Opposite.op ⦋0⦌) d)) ≫ q) y ≫
    eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder e.δ_zero_yonedaEquiv_symm.symm)

/-- 作った族の可変終点は、元の fiber の底上の関手による像そのもの。 -/
lemma initialRestrictionEdgeFamily_endpoint :
    initialRestrictionEdgeFamily p q r hr d hd e y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ SSet.yonedaEquiv.symm e.edge) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q r hr y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q y := by
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialSection p d hd y ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialTotalMap p q r hr d (r.app (Opposite.op ⦋0⦌) d) rfl y ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation q (r.app (Opposite.op ⦋0⦌) d) y) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q y := by
      simp only [initialRestrictionEdgeFamily, Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι]
      erw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnder_eqToHom_projection e.δ_zero_yonedaEquiv_symm.symm]
    _ = _ := by
      simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialTotalMap_evaluation, Category.assoc]
      rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialSection p d hd y)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation p d y),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialSection_evaluation, Category.id_comp]

/-- 比較辺に沿う族は、底の指定頂点上に全単体で留まる。 -/
lemma initialRestrictionEdgeFamily_fixed :
    (initialRestrictionEdgeFamily p q r hr d hd e y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ SSet.yonedaEquiv.symm e.edge)) ≫ q =
        SSet.const y := by
  rw [initialRestrictionEdgeFamily_endpoint, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]

/-- 指定終点の fiber の族として読み直すと、元の底上の関手による fiber の射と厳密に一致。 -/
lemma initialRestrictionEdgeFamily_vertexFiberLift :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift q y
      (initialRestrictionEdgeFamily p q r hr d hd e y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ SSet.yonedaEquiv.symm e.edge))
      (initialRestrictionEdgeFamily_fixed p q r hr d hd e y) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q r hr y := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext q y
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, initialRestrictionEdgeFamily_endpoint]

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
