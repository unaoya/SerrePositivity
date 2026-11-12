module
public import SerrePositivity.KST.Fibration.RelativeSectionBaseChangePoint

/-! # 元の切断比較の指定逆成分は、同じ厳密な pullback 持ち上げ点を回収する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {B D : SSet.{u}} {J : Type u} [Category.{u} J]
  (k : D ⟶ B) (A : Jᵒᵖ ⥤ Over D)

/-- 逆成分は任意の元の切断点を、同じ厳密な底変換逆射の像へ送る。 -/
theorem relativeSectionBaseChangeComponentIso_backward_pointHom
    (X : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) (j : J)
    (v : (((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionEnrichedDiagram (A ⋙ Over.map k)).obj j).obj X).obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberVertexEquiv
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionEnrichedDiagram (A ⋙ Over.map k)).obj j).obj X)).symm v) ≫
      (relativeSectionBaseChangeComponentIso k A X j).inv =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberVertexEquiv
      ((((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionEnrichedDiagram A).precompose
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftFibrationBaseChangeEnriched k)).obj j).obj X)).symm
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeBackward X.val.hom k (A.obj (Opposite.op j)).hom).app
            (Opposite.op ⦋0⦌) v)) := by
  have hv := congrArg (fun m => m.app (Opposite.op ⦋0⦌) v)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeIso X.val.hom k (A.obj (Opposite.op j)).hom).inv_hom_id
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeForward X.val.hom k (A.obj (Opposite.op j)).hom).app
      (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeBackward X.val.hom k (A.obj (Opposite.op j)).hom).app
        (Opposite.op ⦋0⦌) v) = v at hv
  apply (Iso.comp_inv_eq _).2
  have hp := relativeSectionBaseChangeComponentIso_pointHom k A X j
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeBackward X.val.hom k (A.obj (Opposite.op j)).hom).app
      (Opposite.op ⦋0⦌) v)
  rw [hv] at hp
  exact hp.symm

end SerrePositivity.KST.Fibration
