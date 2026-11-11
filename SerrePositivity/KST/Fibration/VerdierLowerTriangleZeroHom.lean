module
public import SerrePositivity.KST.Fibration.VerdierTriangleZeroHom
public import SerrePositivity.KST.Fibration.StableTriangleDiagonalZero

/-! # 元の共有対角を保ち、指定 Verdier 下側二胞体の全長 Hom を零値族へ読む -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 指定した元の Verdier 四角形の下側三角形の同じ二単体。 -/
def verdierLowerTriangle (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋2⦌ :=
  d.square.app (Opposite.op ⦋2⦌) (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1))

/-- 指定した上下二胞体の対角面 δ₁ は、元の同じ一単体として厳密に一致する。 -/
theorem verdierTriangle_sharedDiagonal (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 1 (verdierUpperTriangle d) =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 1 (verdierLowerTriangle d) := by
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 1 (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ d.square)) =
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 1 (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ d.square))
  rw [← stdSimplex.yonedaEquiv_δ_comp, ← stdSimplex.yonedaEquiv_δ_comp,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle_diagonal, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle_diagonal]

/-- 下側二胞体の元の共有対角の零値条件を、上側の同じ対角から移す。 -/
theorem verdierLowerTriangleDiagonal_zero (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    StableArrowZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 1 (verdierLowerTriangle d)) := by
  have hu := stableTriangleDiagonal_zero (verdierUpperTriangle d)
    (verdierUpperTriangle_middle_isZero d)
  exact verdierTriangle_sharedDiagonal d ▸ hu

/-- 元の下側二胞体の全長 Hom は、同じ共有対角により全て零値関手を表す。 -/
theorem verdierLowerTriangleLongHom_zero (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    ∀ v, StableHomZeroVertex ((verdierLowerTriangle d).obj ⟨ULift.up 0⟩)
      ((verdierLowerTriangle d).obj ⟨ULift.up 2⟩)
      ((coherentTriangleLongHom (verdierLowerTriangle d)).app (Opposite.op ⦋0⦌) v) :=
  stableTriangleLongHom_zero_of_diagonal _ (verdierLowerTriangleDiagonal_zero d)

/-- 指定した下側二胞体の元の全長 Hom を、零値完全関手族へ持ち上げる実射。 -/
def verdierLowerTriangleZeroHomLift (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    nerve (CategoryTheory.SimplicialThickening.Path
      (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2)) ⟶
      zeroFunctorLocus ((verdierLowerTriangle d).obj ⟨ULift.up 0⟩)
        ((verdierLowerTriangle d).obj ⟨ULift.up 2⟩) :=
  zeroStableHomFamilyLift _ (verdierLowerTriangleLongHom_zero d)

/-- 元の Kan Hom へ戻すと、指定した下側二胞体の同じ全長 Hom を厳密に回収する。 -/
theorem verdierLowerTriangleZeroHomLift_recovery (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    verdierLowerTriangleZeroHomLift d ≫
        zeroFunctorLocusToStableHom ((verdierLowerTriangle d).obj ⟨ULift.up 0⟩)
          ((verdierLowerTriangle d).obj ⟨ULift.up 2⟩) =
      coherentTriangleLongHom (verdierLowerTriangle d) :=
  zeroStableHomFamilyLift_recovery _ _

/-- 元の全正反復 S• の像でも、指定した下側二胞体の同じ全長 Hom を厳密に回収する。 -/
theorem verdierLowerTriangleZeroHomLift_multi_recovery (r : ℕ) (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    (verdierLowerTriangleZeroHomLift d ≫
        zeroFunctorLocusToStableHom ((verdierLowerTriangle d).obj ⟨ULift.up 0⟩)
          ((verdierLowerTriangle d).obj ⟨ULift.up 2⟩)) ≫
        (stableMultiKanEnrichedFunctor r).map
          ((verdierLowerTriangle d).obj ⟨ULift.up 0⟩)
          ((verdierLowerTriangle d).obj ⟨ULift.up 2⟩) =
      coherentTriangleLongHom ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor r)).app
        (Opposite.op ⦋2⦌) (verdierLowerTriangle d)) :=
  congrArg (fun f => f ≫ (stableMultiKanEnrichedFunctor r).map
    ((verdierLowerTriangle d).obj ⟨ULift.up 0⟩)
    ((verdierLowerTriangle d).obj ⟨ULift.up 2⟩)) (verdierLowerTriangleZeroHomLift_recovery d)

end SerrePositivity.KST.Fibration
