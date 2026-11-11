module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictTransportBaseChangeNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SectionCoreLift
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.VertexFiberNervePullback
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.CocartesianStrictTransportEquivalence

/-!
概要：元の strict transport の under による制限を、同じ始点の fiber で評価する。
方針：頂点評価の前合成則と、底の関手が恒等射を保つことを使う。
規約：評価の標的は元の全空間の同じ fiber。
使われ方：底変換の実際の strict transport 比較の各成分の同値性。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable {C D : Type u} [Category.{u} C] [Category.{u} D] {E : SSet.{u}}
  (p : E ⟶ nerve C) (k : D ⥤ C) (d : D)

/-- 底の関手を合成した始点の表示は、元の底での像の頂点と一致する。 -/
lemma cocartesianStrictTransportRestricted_vertex :
    (nerveMap (Under.forget d) ≫ nerveMap k).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Under.mk (𝟙 d))) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (k.obj d) :=
  nerveMap_app_mk₀ (Under.forget d ⋙ k) (Under.mk (𝟙 d))

/-- under の制限後の section を、元の始点の同じ fiber で評価する。 -/
def cocartesianStrictTransportRestrictedEvaluate :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p (nerveMap (Under.forget d) ≫ nerveMap k) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (k.obj d)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsEvaluate p (nerveMap (Under.forget d) ≫ nerveMap k)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Under.mk (𝟙 d))) ≫
      eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p) (cocartesianStrictTransportRestricted_vertex k d))

/-- 頂点の表示を揃えた同じ評価は、包含後に元の全空間への評価となる。 -/
lemma cocartesianStrictTransportRestrictedEvaluate_ι :
    cocartesianStrictTransportRestrictedEvaluate p k d ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (k.obj d)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionEvaluate p (nerveMap (Under.forget d) ≫ nerveMap k)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Under.mk (𝟙 d))) := by
  unfold cocartesianStrictTransportRestrictedEvaluate
  rw [Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.vertexFiberTransport_ι p (cocartesianStrictTransportRestricted_vertex k d)]
  rfl

/-- under の関手は、恒等射の始点頂点を同じ恒等射の頂点へ写す。 -/
lemma cocartesianStrictTransportUnderPost_vertex :
    (nerveMap (Under.post k)).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Under.mk (𝟙 d))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Under.mk (𝟙 (k.obj d))) := by
  apply (nerveEquiv (C := Under (k.obj d))).injective
  change Under.mk (k.map (𝟙 d)) = Under.mk (𝟙 (k.obj d))
  rw [k.map_id]

/-- under に沿って制限した後の始点評価は、元の strict transport の同じ始点評価。 -/
lemma cocartesianStrictTransportUnderPost_evaluate :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre p (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportUnderPost k d) ≫
      cocartesianStrictTransportRestrictedEvaluate p k d =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportEvaluate p (k.obj d) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (k.obj d))
  rw [Category.assoc, cocartesianStrictTransportRestrictedEvaluate_ι]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre p (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportUnderPost k d) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionEvaluate p (nerveMap (Under.forget d) ≫ nerveMap k)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Under.mk (𝟙 d))) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionEvaluate p (nerveMap (Under.forget (k.obj d)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Under.mk (𝟙 (k.obj d))))
  refine (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionEvaluate_overPre p (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportUnderPost k d)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Under.mk (𝟙 d)))).trans ?_
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionEvaluate p (nerveMap (Under.forget (k.obj d)))
    ((nerveMap (Under.post k)).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Under.mk (𝟙 d)))) = _
  rw [cocartesianStrictTransportUnderPost_vertex]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
