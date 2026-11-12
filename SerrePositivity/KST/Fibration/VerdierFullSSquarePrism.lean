module
public import SerrePositivity.KST.Fibration.VerdierFullSUpperPrism
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SquarePrismGluing

/-!
概要：指定 Verdier 四角形の上側中間対象変更を、元の下側二胞体を固定した全四角柱へ延ばす。
方針：共有対角を固定した上側三角柱と定値の下側三角柱を公開押し出しで貼る。
規約：終端は元の全四角形、下側二胞体は全時刻で厳密固定。核四角形との同定は別工程。
使われ方：K-6 c4 の Ex∞ 上の全四角形比較の指定 Verdier 側。
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
variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})

/-- 指定上側の始端二胞体の対角は、元の四角形の共有対角そのもの。 -/
theorem verdierFullSTransportedUpper_diagonal :
    stdSimplex.δ (1 : Fin 3) ≫ zeroMiddleFullSKanTransportedTriangle (verdierUpperTriangle d)
        (verdierUpperTriangle_middle_isZero d) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareDiagonal ≫ (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0)) := by
  unfold zeroMiddleFullSKanTransportedTriangle
  erw [← Category.assoc, stdSimplex.δ_comp_δ (by decide : (1 : Fin 3) ≤ 1), Category.assoc,
    zeroMiddleFullSKanTetrahedron_original, verdierFullSUpperPrism_original,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle_diagonal]

/-- 同じ全 S• 始端上側二胞体と元の下側二胞体を持つ、指定した一つの全四角形。 -/
def verdierFullSTransportedSquare : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.desc
    (zeroMiddleFullSKanTransportedTriangle (verdierUpperTriangle d)
      (verdierUpperTriangle_middle_isZero d))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0)))
    ((verdierFullSTransportedUpper_diagonal d).trans (by
      simpa only [Category.assoc] using! congrArg
        (fun f => f ≫ (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0)))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle_diagonal (1 : Fin 2)).symm))

/-- 同じ始端全四角形の上側は、指定した実充填からの全 S• 二胞体。 -/
theorem verdierFullSTransportedSquare_upper :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ verdierFullSTransportedSquare d =
      zeroMiddleFullSKanTransportedTriangle (verdierUpperTriangle d)
        (verdierUpperTriangle_middle_isZero d) := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inl_desc _ _ _

/-- 同じ始端全四角形の下側は、元の指定下側二胞体そのもの。 -/
theorem verdierFullSTransportedSquare_lower :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ verdierFullSTransportedSquare d =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inr_desc _ _ _

/-- 同じ始端全四角形の上側を、元の指定上側二胞体へ送る同じ実三角柱。 -/
def verdierFullSSquareUpperPrism : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ verdierFullSTransportedSquare d)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0))) where
  h := (verdierFullSUpperPrism d).h
  h₀ := (verdierFullSUpperPrism d).h₀.trans (verdierFullSTransportedSquare_upper d).symm
  h₁ := (verdierFullSUpperPrism d).h₁
  rel := by ext n t; exact False.elim t.1.2

/-- 元の指定下側二胞体は、同じ全四角柱の下側で全時刻固定する。 -/
def verdierFullSSquareLowerPrism : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ verdierFullSTransportedSquare d)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0))) where
  h := fst (Δ[2] : SSet.{u + 1}) Δ[1] ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0)))
  h₀ := by
    have h := (SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0))))).h₀
    exact h.trans (verdierFullSTransportedSquare_lower d).symm
  h₁ := (SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0))))).h₁
  rel := by ext n t; exact False.elim t.1.2

/-- 同じ上側三角柱と固定下側三角柱は、元の共有対角で全パラメーター一致する。 -/
theorem verdierFullSSquarePrism_diagonal :
    (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫ (verdierFullSSquareUpperPrism d).h =
      (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫ (verdierFullSSquareLowerPrism d).h := by
  change _ ≫ (verdierFullSUpperPrism d).h = _
  rw [verdierFullSUpperPrism_diagonal]
  erw [verdierFullSTransportedUpper_diagonal]
  change fst (Δ[1] : SSet.{u + 1}) Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareDiagonal ≫ _ =
    (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
      (fst (Δ[2] : SSet.{u + 1}) Δ[1] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ _))
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle_diagonal (1 : Fin 2), Category.assoc]
  ext n t
  rfl

/-- 元の上下二胞体を保持して貼った、同じ全四角形への実四角柱。 -/
def verdierFullSSquarePrism : SSet.Homotopy (verdierFullSTransportedSquare d)
    (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0)) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareHomotopyOfTriangleHomotopies (verdierFullSSquareUpperPrism d)
    (verdierFullSSquareLowerPrism d) (verdierFullSSquarePrism_diagonal d)

end SerrePositivity.KST.Fibration
