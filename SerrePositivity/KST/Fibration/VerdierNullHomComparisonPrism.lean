module
public import SerrePositivity.KST.Fibration.VerdierNullHomRelativeComparison
public import SerrePositivity.KST.Fibration.FixedRestrictionFunctorPrism

/-! # 指定 Verdier 上下二胞体族の比較円柱と、元の共有対角の全時刻固定 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 元の上下二胞体の全 Hom 族を結ぶ、共有対角上恒等の同じ全円柱。 -/
def verdierNullHomComparisonPrism (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :
    (Δ[1] : SSet.{u}) ⊗ nerve (CategoryTheory.SimplicialThickening.Path
      (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2)) ⟶
      ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩ ⟶[SSet.{u}]
        (verdierNullDiagonal d).obj ⟨ULift.up 1⟩) :=
  (verdierNullHomRelativeComparison d j k).prism

/-- 元の共有対角上の比較円柱は、同じ直接 path の値を全時刻にわたり厳密に保つ。 -/
theorem verdierNullHomComparisonPrism_diagonal (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :
    (Δ[1] ◁ coherentTriangleDirectVertexMap) ≫ verdierNullHomComparisonPrism d j k =
      snd (Δ[1] : SSet.{u}) (Δ[0] : SSet.{u}) ≫
        coherentTriangleDirectVertexMap ≫ verdierNullHomFamily d j :=
  (verdierNullHomRelativeComparison d j k).prism_restriction

/-- 元の正反復 S• の同じ全 Hom 作用後も、共有対角上の全時刻固定を保つ。 -/
theorem verdierNullHomComparisonPrism_multi_diagonal (r : ℕ) (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})
    (j k : Fin 2) :
    (Δ[1] ◁ coherentTriangleDirectVertexMap) ≫
        (verdierNullHomRelativeMultiComparison r d j k).prism =
      snd (Δ[1] : SSet.{u}) (Δ[0] : SSet.{u}) ≫ coherentTriangleDirectVertexMap ≫
        (verdierNullHomFamily d j ≫ (stableMultiKanEnrichedFunctor r).map
          ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)
          ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩)) :=
  (verdierNullHomRelativeMultiComparison r d j k).prism_restriction

end SerrePositivity.KST.Fibration
