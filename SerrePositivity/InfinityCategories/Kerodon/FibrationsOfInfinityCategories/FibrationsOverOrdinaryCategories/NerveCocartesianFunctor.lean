module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LiftPreservation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveCocartesianFibration

/-!
概要：係数の自然変換が誘導する weighted nerve の射は全 cocartesian 辺を保つ。
方針：可逆な最後の係数を持つ lift を選び、比較三角形から全辺の保存へ戻す。
規約：自然変換の成分に同値性は要求せず、係数の quasicategory 性だけを使う。
使われ方：Cat∞ 値 unstraightening の関手性と相対 Hom の制限。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 係数の自然変換は最後の係数の可逆性を保つ。 -/
lemma weightedNerveMap_coefficientInvertible {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} (η : F ⟶ G) (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) _⦋1⦌)
    (he : _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.WeightedNerveCoefficientInvertible F e) :
    _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.WeightedNerveCoefficientInvertible G ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap η).app _ e) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv
    (e.2.app (Fin.last 1) ≫ η.app (e.1.obj (Fin.last 1)))))
  rw [SSet.yonedaEquiv_comp]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv (e.2.app (Fin.last 1)))).map
      ((truncation 2).map (η.app (e.1.obj (Fin.last 1)))))
    (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((η.app (e.1.obj (Fin.last 1))).app _
      (SSet.yonedaEquiv (e.2.app (Fin.last 1))))) rfl).mp
    (he.map (η.app (e.1.obj (Fin.last 1))))

/-- 任意の係数自然変換による weighted nerve の実際の射は全 cocartesian 辺を保つ。 -/
lemma weightedNerveMap_preservesCocartesianEdges {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} [∀ c, Quasicategory (F.obj c)] [∀ c, Quasicategory (G.obj c)]
    (η : F ⟶ G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PreservesCocartesianEdges (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection G)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap η) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.preservesCocartesianEdges_of_matching_lifts
  intro e
  have hsrc : stdSimplex.δ 1 ≫
      SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F).app (Opposite.op ⦋1⦌) e) =
        SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F).app (Opposite.op ⦋0⦌)
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F).δ 1 e)) := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]
    apply congrArg SSet.yonedaEquiv.symm
    exact (ConcreteCategory.congr_hom
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F).naturality (SimplexCategory.δ (1 : Fin 2)).op) e).symm
  obtain ⟨H, hHsrc, hHbase, hi⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.exists_weightedNerve_lift_with_invertible_coefficient F
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F).δ 1 e) (SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F).app _ e)) hsrc
  refine ⟨SSet.yonedaEquiv H, ?_, ?_,
    _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.isCocartesianEdge_weightedNerve_of_coefficient F _ hi,
    _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.isCocartesianEdge_weightedNerve_of_coefficient G _
      (weightedNerveMap_coefficientInvertible η _ hi)⟩
  · rw [← stdSimplex.yonedaEquiv_δ_comp, hHsrc, Equiv.apply_symm_apply]
  · rw [← SSet.yonedaEquiv_comp, hHbase, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
