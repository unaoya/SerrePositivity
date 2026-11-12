module
public import SerrePositivity.KST.Fibration.ZeroStableHomRelativeComparison
public import SerrePositivity.KST.Fibration.VerdierNullHomFamilies

/-! # 指定 Verdier 上下二胞体の、元の共有対角上で恒等となる全 Hom の比較 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 元の長 path の nerve における、同じ直接 path の実頂点の包含。 -/
def coherentTriangleDirectVertexMap : (Δ[0] : SSet.{u}) ⟶
    nerve (CategoryTheory.SimplicialThickening.Path
      (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2)) :=
  SSet.yonedaEquiv.symm (ComposableArrows.mk₀ coherentTriangleDirectPath)

instance coherentTriangleDirectVertexMap_mono : Mono (coherentTriangleDirectVertexMap.{u}) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro x y _hxy
  apply SSet.stdSimplex.ext
  intro k
  apply Fin.ext
  omega

/-- 指定した上下二胞体族は、同じ直接 path 上で厳密に同じ関手族に制限される。 -/
theorem verdierNullHomFamily_same_direct (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :
    coherentTriangleDirectVertexMap ≫ verdierNullHomFamily d j =
      coherentTriangleDirectVertexMap ≫ verdierNullHomFamily d k := by
  rw [coherentTriangleDirectVertexMap, SSet.yonedaEquiv_symm_comp,
    SSet.yonedaEquiv_symm_comp, verdierNullHomFamily_direct, verdierNullHomFamily_direct]

/-- 元の上下二胞体族を、共有対角上の制限が同じ恒等一単体となる全可逆辺で結ぶ。 -/
def verdierNullHomRelativeComparison (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :
    FixedRestrictionFunctorEdge coherentTriangleDirectVertexMap
      (verdierNullHomFamily d j) (verdierNullHomFamily d k) :=
  zeroStableHomFamilyRelativeComparison _ _ _ (verdierNullHomFamily_zero d j)
    (verdierNullHomFamily_zero d k) (verdierNullHomFamily_same_direct d j k)

/-- 同じ対角上恒等の実比較辺から得る、元の両二胞体族の全関手同型。 -/
def verdierNullHomRelativeIso (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (verdierNullHomFamily d j) (verdierNullHomFamily d k) :=
  (verdierNullHomRelativeComparison d j k).iso

/-- 元の全正反復 S• の全 Hom 作用後も、同じ共有対角上で恒等の全比較辺を保つ。 -/
def verdierNullHomRelativeMultiComparison (r : ℕ) (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :
    FixedRestrictionFunctorEdge coherentTriangleDirectVertexMap
      (verdierNullHomFamily d j ≫ (stableMultiKanEnrichedFunctor r).map
        ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩) ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩))
      (verdierNullHomFamily d k ≫ (stableMultiKanEnrichedFunctor r).map
        ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩) ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩)) :=
  (verdierNullHomRelativeComparison d j k).postcomp ((stableMultiKanEnrichedFunctor r).map
    ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩) ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩))

end SerrePositivity.KST.Fibration
