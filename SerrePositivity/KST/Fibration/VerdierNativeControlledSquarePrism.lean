module
public import SerrePositivity.KST.Fibration.VerdierNativeControlledSquare

/-!
概要：実 (9b) 欠面から元の指定 Verdier 四角形へ、同じ対角固定四角柱を構成する。
方針：同じ制御上側三角柱と元の下側の定値三角柱を全共有対角で貼る。
規約：元の実充填・全二胞体を保持し、新しい存在仮定を取らない。
使われ方：K-6 c4 の有限始端照合後の元の四角形への実復帰。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (t : (Δ[1] : SSet.{u + 1}) _⦋0⦌)

/-- 概要：同じ始端全四角形の上側を、元の指定上側二胞体へ送る同じ実三角柱。
方針：同じ実制御三角柱と元の下側の貼り合わせを使う。
規約：新しい存在仮定なし。使われ方：指定有限始端照合後の全四角形比較。 -/
def verdierNativeControlledSquareUpperPrism : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ verdierNativeControlledSquare d t)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0))) where
  h := (verdierNativeControlledUpperPrism d t).h
  h₀ := (verdierNativeControlledUpperPrism d t).h₀.trans (verdierNativeControlledSquare_upper d t).symm
  h₁ := (verdierNativeControlledUpperPrism d t).h₁
  rel := by ext n t; exact False.elim t.1.2

/-- 概要：元の指定下側二胞体は、同じ全四角柱の下側で全時刻固定する。
方針：同じ実制御三角柱と元の下側の貼り合わせを使う。
規約：新しい存在仮定なし。使われ方：指定有限始端照合後の全四角形比較。 -/
def verdierNativeControlledSquareLowerPrism : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ verdierNativeControlledSquare d t)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0))) where
  h := fst (Δ[2] : SSet.{u + 1}) Δ[1] ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0)))
  h₀ := by
    have h := (SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0))))).h₀
    exact h.trans (verdierNativeControlledSquare_lower d t).symm
  h₁ := (SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0))))).h₁
  rel := by ext n t; exact False.elim t.1.2

/-- 概要：同じ上側三角柱と固定下側三角柱は、元の共有対角で全パラメーター一致する。
方針：同じ実制御三角柱と元の下側の貼り合わせを使う。
規約：新しい存在仮定なし。使われ方：指定有限始端照合後の全四角形比較。 -/
theorem verdierNativeControlledSquarePrism_diagonal :
    (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫ (verdierNativeControlledSquareUpperPrism d t).h =
      (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫ (verdierNativeControlledSquareLowerPrism d t).h := by
  change _ ≫ (verdierNativeControlledUpperPrism d t).h = _
  rw [verdierNativeControlledUpperPrism_diagonal]
  erw [verdierNativeControlledUpper_diagonal]
  change fst (Δ[1] : SSet.{u + 1}) Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareDiagonal ≫ _ =
    (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
      (fst (Δ[2] : SSet.{u + 1}) Δ[1] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ _))
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle_diagonal (1 : Fin 2), Category.assoc]
  ext n t
  rfl

/-- 概要：元の上下二胞体を保持して貼った、同じ全四角形への実四角柱。
方針：同じ実制御三角柱と元の下側の貼り合わせを使う。
規約：新しい存在仮定なし。使われ方：指定有限始端照合後の全四角形比較。 -/
def verdierNativeControlledSquarePrism : SSet.Homotopy (verdierNativeControlledSquare d t)
    (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0)) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareHomotopyOfTriangleHomotopies (verdierNativeControlledSquareUpperPrism d t)
    (verdierNativeControlledSquareLowerPrism d t) (verdierNativeControlledSquarePrism_diagonal d t)

end SerrePositivity.KST.Fibration
