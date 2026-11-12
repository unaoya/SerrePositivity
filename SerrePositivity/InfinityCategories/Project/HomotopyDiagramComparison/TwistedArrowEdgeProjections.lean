module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.TwistedArrowEdgeCospan
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.IdentityCoordinates

/-!
概要：同じ二つの Tw 辺の底への射影を、元の辺と恒等辺へ厳密に照合する。
方針：重みの左右の包含を標準三単体の座標へ移して計算する。
規約：元の辺とその反転を使用し、別の同じ Hom 類の代表へ置き換えない。
使われ方：同じ Tw 全体の復元射による、二方向の恒等点輸送の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 始点側 Tw 辺の右射影は元の辺自身。 -/
lemma twistedArrowSourceEdgeSimplex_right {C : SSet.{u}} (f : (Δ[1] : SSet.{u}) ⟶ C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight C).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowSourceEdgeSimplex f) =
      SSet.yonedaEquiv f := by
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso 1).hom ≫
    stdSimplex.map (SimplexCategory.mkHom _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowSourceEdgeOrderHom) ≫ f) = _
  have h : SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightOrderHom 1 1) ≫
      SimplexCategory.mkHom _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowSourceEdgeOrderHom = 𝟙 ⦋1⦌ := by
    ext i
    fin_cases i <;> rfl
  have hm : stdSimplex.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightOrderHom 1 1)) ≫
      stdSimplex.map (SimplexCategory.mkHom _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowSourceEdgeOrderHom) =
        (𝟙 (Δ[1] : SSet.{u})) := by
    have hm := congrArg (fun g : ⦋1⦌ ⟶ ⦋1⦌ ↦ (stdSimplex.{u}).map g) h
    rw [Functor.map_comp] at hm
    exact hm.trans (stdSimplex.map_id _)
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ _), _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso_inr,
    ← Category.assoc, hm, Category.id_comp]

/-- 終点側 Tw 辺の左射影は元の辺の同じ反転単体。 -/
lemma twistedArrowTargetEdgeSimplex_left {C : SSet.{u}} (f : (Δ[1] : SSet.{u}) ⟶ C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft C).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowTargetEdgeSimplex f) =
      SSet.opObjEquiv.symm (SSet.yonedaEquiv f) := by
  change SSet.opObjEquiv.symm (SSet.yonedaEquiv ((stdSimplex.opIso ⦋1⦌).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso 1).hom ≫
      stdSimplex.map (SimplexCategory.mkHom _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowTargetEdgeOrderHom) ≫ f)) = _
  have h : SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinLeftOrderHom 1 1) ≫
      SimplexCategory.mkHom _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowTargetEdgeOrderHom = 𝟙 ⦋1⦌ := by
    ext i
    fin_cases i <;> rfl
  have hm : stdSimplex.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinLeftOrderHom 1 1)) ≫
      stdSimplex.map (SimplexCategory.mkHom _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowTargetEdgeOrderHom) =
        (𝟙 (Δ[1] : SSet.{u})) := by
    have hm := congrArg (fun g : ⦋1⦌ ⟶ ⦋1⦌ ↦ (stdSimplex.{u}).map g) h
    rw [Functor.map_comp] at hm
    exact hm.trans (stdSimplex.map_id _)
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _), _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso_inl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, hm, Category.id_comp]

/-- 終点側 Tw 辺の右射影は、元の終点の恒等辺。 -/
lemma twistedArrowTargetEdgeSimplex_right {C : SSet.{u}} (f : (Δ[1] : SSet.{u}) ⟶ C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight C).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowTargetEdgeSimplex f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1)) 1 := by
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso 1).hom ≫
    stdSimplex.map (SimplexCategory.mkHom _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowTargetEdgeOrderHom) ≫ f) =
      SSet.yonedaEquiv (SSet.const _)
  have h : SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightOrderHom 1 1) ≫
      SimplexCategory.mkHom _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowTargetEdgeOrderHom =
        SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowConstantEdgeOrderHom 1) := by
    ext i
    fin_cases i <;> rfl
  have hm : stdSimplex.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightOrderHom 1 1)) ≫
      stdSimplex.map (SimplexCategory.mkHom _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowTargetEdgeOrderHom) =
        (stdSimplex.{u}).map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowConstantEdgeOrderHom 1)) := by
    simpa only [Functor.map_comp] using
      congrArg (fun g : ⦋1⦌ ⟶ ⦋1⦌ ↦ (stdSimplex.{u}).map g) h
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ _), _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso_inr,
    ← Category.assoc, hm, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowConstantEdgeOrderHom_comp]

/-- 始点側 Tw 辺の左射影は、元の始点の反転した恒等辺。 -/
lemma twistedArrowSourceEdgeSimplex_left {C : SSet.{u}} (f : (Δ[1] : SSet.{u}) ⟶ C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft C).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowSourceEdgeSimplex f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
        (SSet.opObjEquiv.symm (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0))) 1 := by
  change SSet.opObjEquiv.symm (SSet.yonedaEquiv ((stdSimplex.opIso ⦋1⦌).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso 1).hom ≫
      stdSimplex.map (SimplexCategory.mkHom _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowSourceEdgeOrderHom) ≫ f)) = _
  apply SSet.opObjEquiv.injective
  simp only [Equiv.apply_symm_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.constant_opObjEquiv]
  change SSet.yonedaEquiv ((stdSimplex.opIso ⦋1⦌).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso 1).hom ≫
      stdSimplex.map (SimplexCategory.mkHom _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowSourceEdgeOrderHom) ≫ f) =
        SSet.yonedaEquiv (SSet.const _)
  have h : SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinLeftOrderHom 1 1) ≫
      SimplexCategory.mkHom _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowSourceEdgeOrderHom =
        SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowConstantEdgeOrderHom 0) := by
    ext i
    fin_cases i <;> rfl
  have hm : stdSimplex.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinLeftOrderHom 1 1)) ≫
      stdSimplex.map (SimplexCategory.mkHom _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowSourceEdgeOrderHom) =
        (stdSimplex.{u}).map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowConstantEdgeOrderHom 0)) := by
    simpa only [Functor.map_comp] using
      congrArg (fun g : ⦋1⦌ ⟶ ⦋1⦌ ↦ (stdSimplex.{u}).map g) h
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _), _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso_inl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, hm, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowConstantEdgeOrderHom_comp]

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
