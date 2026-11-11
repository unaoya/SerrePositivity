module

public import SerrePositivity.KST.Spectra.CoherentTrianglePathMinimum
public import SerrePositivity.KST.Spectra.CoherentTriangleTraceRecovery
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedConeSimplex

/-!
概要：weighted cone の元の二単体の Hom 経路を、反転した係数の元の一単体で計算する。
方針：最小点座標の厳密式で path 区間を消去し、区間の反転同型を明示する。
規約：元の係数と反転の向きを保持。使われ方：元の円評価錐との二つの三角形の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.CoherentPathCoordinates
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 元の weighted cone の二単体の経路は、反転係数の元の一単体の評価そのもの。 -/
lemma weightedConeSimplex_triangleTrace (F : I ⥤ C) (x : C)
    {σ : ComposableArrows I 1}
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight 1 ⟶ σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor) :
    triangleTrace (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeSimplex F x τ) =
      (stdSimplex.opIso ⦋1⦌).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap (τ.app (1 : Fin 2)) := by
  change trianglePathInterval ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimumMap (1 : Fin 2) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap (τ.app (1 : Fin 2))) = _
  rw [← Category.assoc, trianglePathInterval_minimum]

/-- 同じ係数の式は、元の二単体の長い Hom の作用全体を回収する。 -/
lemma weightedConeSimplex_longHom (F : I ⥤ C) (x : C)
    {σ : ComposableArrows I 1}
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight 1 ⟶ σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeSimplex F x τ).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap (0 : Fin 2) ≫
        (stdSimplex.opIso ⦋1⦌).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap (τ.app (1 : Fin 2)) := by
  rw [← triangleTrace_recover, weightedConeSimplex_triangleTrace]

end SerrePositivity.KST.Spectra.CoherentPathCoordinates
