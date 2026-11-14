module
public import SerrePositivity.KST.Fibration.StableTriangleZeroHom
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.MapSmallness

/-! # 指定 Verdier 四角形の上側二胞体の、元の全零値 Hom への読み出し -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 指定した元の Verdier 四角形の上側三角形の同じ二単体。 -/
def verdierUpperTriangle (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋2⦌ :=
  d.square.app (Opposite.op ⦋2⦌) (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0))

/-- 元の上側二単体の初頂点は、元の四角形の同じ初頂点を表す安定圏。 -/
theorem verdierUpperTriangle_source (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    (verdierUpperTriangle d).obj ⟨ULift.up 0⟩ = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex d.square 0 0) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentMap_simplex_obj d.square (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0)) ⟨ULift.up 0⟩

/-- 元の上側二単体の中間頂点は、指定した元の零角を表す安定圏。 -/
theorem verdierUpperTriangle_middle (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    (verdierUpperTriangle d).obj ⟨ULift.up 1⟩ = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex d.square 0 1) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentMap_simplex_obj d.square (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0)) ⟨ULift.up 1⟩

/-- 元の上側二単体の終頂点は、元の四角形の同じ終頂点を表す安定圏。 -/
theorem verdierUpperTriangle_target (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    (verdierUpperTriangle d).obj ⟨ULift.up 2⟩ = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex d.square 1 1) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentMap_simplex_obj d.square (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0)) ⟨ULift.up 2⟩

/-- 指定 Verdier 四角形の同じ上側二単体の中間安定圏は全対象が零。 -/
theorem verdierUpperTriangle_middle_isZero (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory ((verdierUpperTriangle d).obj ⟨ULift.up 1⟩) :=
  (verdierUpperTriangle_middle d).symm ▸ d.zero_corner

/-- 指定した上側二胞体の元の全長 Hom は、全頂点で同じ零値関手条件を満たす。 -/
theorem verdierUpperTriangleLongHom_zero (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    ∀ v, StableHomZeroVertex ((verdierUpperTriangle d).obj ⟨ULift.up 0⟩)
      ((verdierUpperTriangle d).obj ⟨ULift.up 2⟩)
      ((coherentTriangleLongHom (verdierUpperTriangle d)).app (Opposite.op ⦋0⦌) v) :=
  stableTriangleLongHom_zero _ (verdierUpperTriangle_middle_isZero d)

/-- 指定した元の上側二胞体の全長 Hom を零値部分複体へ読み出す実射。 -/
def verdierUpperTriangleZeroHomLift (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    nerve (SimplicialThickening.Path
      (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2)) ⟶
      zeroFunctorLocus ((verdierUpperTriangle d).obj ⟨ULift.up 0⟩)
        ((verdierUpperTriangle d).obj ⟨ULift.up 2⟩) :=
  stableTriangleZeroHomLift _ (verdierUpperTriangle_middle_isZero d)

/-- 元の Kan Hom へ戻すと、指定した元の上側二胞体の全長 Hom と厳密に一致する。 -/
theorem verdierUpperTriangleZeroHomLift_recovery (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    verdierUpperTriangleZeroHomLift d ≫
        zeroFunctorLocusToStableHom ((verdierUpperTriangle d).obj ⟨ULift.up 0⟩)
          ((verdierUpperTriangle d).obj ⟨ULift.up 2⟩) =
      coherentTriangleLongHom (verdierUpperTriangle d) :=
  stableTriangleZeroHomLift_recovery _ _

/-- 元の正反復 S• の像でも、指定した上側二胞体の全長 Hom を厳密に回収する。 -/
theorem verdierUpperTriangleZeroHomLift_multi_recovery (r : ℕ) (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    (verdierUpperTriangleZeroHomLift d ≫
        zeroFunctorLocusToStableHom ((verdierUpperTriangle d).obj ⟨ULift.up 0⟩)
          ((verdierUpperTriangle d).obj ⟨ULift.up 2⟩)) ≫
        (stableMultiKanEnrichedFunctor r).map
          ((verdierUpperTriangle d).obj ⟨ULift.up 0⟩)
          ((verdierUpperTriangle d).obj ⟨ULift.up 2⟩) =
      coherentTriangleLongHom ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor r)).app
        (Opposite.op ⦋2⦌) (verdierUpperTriangle d)) :=
  congrArg (fun f => f ≫ (stableMultiKanEnrichedFunctor r).map
    ((verdierUpperTriangle d).obj ⟨ULift.up 0⟩)
    ((verdierUpperTriangle d).obj ⟨ULift.up 2⟩)) (verdierUpperTriangleZeroHomLift_recovery d)

end SerrePositivity.KST.Fibration
