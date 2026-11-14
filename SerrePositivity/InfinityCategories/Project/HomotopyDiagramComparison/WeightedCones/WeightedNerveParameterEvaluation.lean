module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.WeightedSectionsParameters
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedSectionParameter
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NerveTensor
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveFunctor

/-!
概要：係数図式のパラメータ付き射と weighted nerve の普遍評価を照合する。
方針：全初区間の二つのパラメータを対にし、係数での評価を比較する。
規約：追加パラメータを頂点へ落とさず、単体集合の射の等式を示す。
使われ方：HTT 4.2.4.1 の end の豊穣作用と実際の coherent な錐の族の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {I : Type u} [SmallCategory I] {H H' : I ⥤ SSet.{u}} {A B : SSet.{u}}

/-- パラメータ付き係数変換の各初区間は、元の評価と追加パラメータの同時評価。 -/
lemma weightedNerveCoefficients_parameter_transform
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I ⊗ (Functor.const I).obj A ⟶ H)
    (η : H ⋙ tensorRight B ⟶ H') {n : ℕ} (σ : ComposableArrows I n)
    (a : Δ[n] ⟶ A) (b : Δ[n] ⟶ B) (j : Fin (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveCoefficients (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionParameterTransform s η) σ (lift a b)).app j =
      lift ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveCoefficients s σ a).app j)
        (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion j.val n (Nat.le_of_lt_succ j.isLt)) ≫ b) ≫
          η.app (σ.obj j) := by
  change lift ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverWeight σ).app j)
      (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion j.val n (Nat.le_of_lt_succ j.isLt)) ≫
        lift a b) ≫ (α_ _ A B).inv ≫ (s.app (σ.obj j) ▷ B) ≫ η.app (σ.obj j) =
    lift (lift ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverWeight σ).app j)
      (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion j.val n (Nat.le_of_lt_succ j.isLt)) ≫ a) ≫
        s.app (σ.obj j))
      (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion j.val n (Nat.le_of_lt_succ j.isLt)) ≫ b) ≫
        η.app (σ.obj j)
  rw [comp_lift, lift_lift_associator_inv_assoc, lift_whiskerRight_assoc]

/-- 係数のパラメータ付き変換から作る切断は、weighted nerve の同じ変換による評価。 -/
lemma weightedNerveSectionFromTransform_parameter_transform
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I ⊗ (Functor.const I).obj A ⟶ H)
    (η : H ⋙ tensorRight B ⟶ H') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedNerveSectionFromTransform (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionParameterTransform s η) =
      (α_ (nerve I) A B).inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedNerveSectionFromTransform s ▷ B) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveTensorMap H B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap η := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, a, b⟩
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  apply NatTrans.ext
  funext j
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveCoefficients (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionParameterTransform s η) σ
      (SSet.yonedaEquiv.symm (a, b))).app j =
    lift ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveCoefficients s σ (SSet.yonedaEquiv.symm a)).app j)
      (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion j.val n (Nat.le_of_lt_succ j.isLt)) ≫
        SSet.yonedaEquiv.symm b) ≫ η.app (σ.obj j)
  exact weightedNerveCoefficients_parameter_transform s η σ
    (SSet.yonedaEquiv.symm a) (SSet.yonedaEquiv.symm b) j

/-- end の全パラメータの作用と weighted nerve の普遍評価は厳密に可換。 -/
lemma bousfieldKanWeightedNerveEvaluation_parameter_map (η : H ⋙ tensorRight B ⟶ H') :
    (nerve I ◁ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsParameterMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) η) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeightedNerveEvaluation H' =
      (α_ (nerve I) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim H) B).inv ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeightedNerveEvaluation H ▷ B) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveTensorMap H B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap η := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanSectionHomEquiv_apply]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedNerveSectionFromTransform
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsParameterMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) η)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsParameterMap_uncurry,
    weightedNerveSectionFromTransform_parameter_transform]
  rfl

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
