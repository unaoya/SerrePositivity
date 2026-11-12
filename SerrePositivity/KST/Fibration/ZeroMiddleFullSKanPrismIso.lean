module
public import SerrePositivity.KST.Fibration.ZeroMiddleFullSKanPrismFaces
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise

/-!
概要：元の二胞体を端面に持つ全 S• 三角柱の、指定辺そのものの可逆性。
方針：両端の縦辺は恒等、中間縦辺は同じ全 S• 比較と厳密照合する。
規約：点ごとの可逆性を公開判定で全関手同型へ束ね、元の三角柱を保持する。
使われ方：K-6 c4 の全四角形比較へ貼り合わせる上側の実三角柱同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋2⦌) (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (s.obj ⟨ULift.up 1⟩))

/-- 元の実三角柱の中間縦辺は、同じ元の全 S• 比較の全一単体そのもの。 -/
theorem zeroMiddleFullSKanPrism_middle_edge :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (zeroMiddleFullSKanPrism s hZ)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 3))).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (zeroMiddleFullSKanComparison s hZ)).edge := by
  have he : stdSimplex.δ (0 : Fin 3) ≫
      (stdSimplex.δ (3 : Fin 4) ≫ zeroMiddleFullSKanTetrahedron s hZ) =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (zeroMiddleFullSKanComparison s hZ)).edge := by
    rw [zeroMiddleFullSKanTetrahedron_first]
    exact (zeroMiddleFullSKanFirstTriangle s hZ).δ_zero_yonedaEquiv_symm
  have he' : SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫
      (stdSimplex.δ (3 : Fin 4) ≫ zeroMiddleFullSKanTetrahedron s hZ)) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (zeroMiddleFullSKanComparison s hZ)).edge :=
    (congrArg SSet.yonedaEquiv he).trans (SSet.yonedaEquiv.apply_symm_apply _)
  rw [← he']
  change (zeroMiddleFullSKanTetrahedron s hZ).app (Opposite.op ⦋1⦌) _ =
    (zeroMiddleFullSKanTetrahedron s hZ).app (Opposite.op ⦋1⦌) _
  congr 1 <;> (apply SSet.stdSimplex.ext; intro i; fin_cases i <;> rfl)

/-- 同じ元の三角柱は、三つの各頂点で可逆な実縦辺を持つ。 -/
theorem zeroMiddleFullSKanPrism_pointwise :
    ∀ k : (Δ[2] : SSet.{u + 1}) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (zeroMiddleFullSKanPrism s hZ) k).toTruncated := by
  intro k
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective k
  fin_cases j
  · have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (zeroMiddleFullSKanPrism s hZ)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 3))).edge =
      (Truncated.Edge.id (X := (truncation 2).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
        ((zeroMiddleFullSKanTetrahedron s hZ).app (Opposite.op ⦋0⦌)
          (stdSimplex.obj₀Equiv.symm (0 : Fin 4)))).edge := by
      change (zeroMiddleFullSKanTetrahedron s hZ).app (Opposite.op ⦋1⦌) _ =
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.σ 0 ((zeroMiddleFullSKanTetrahedron s hZ).app (Opposite.op ⦋0⦌) _)
      rw [← σ_naturality_apply]
      congr 1 <;> (apply SSet.stdSimplex.ext; intro i; fin_cases i <;> rfl)
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr
    change IsIso (Truncated.HomotopyCategory.homMk (Truncated.Edge.id _))
    rw [Truncated.HomotopyCategory.homMk_id]
    infer_instance
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (zeroMiddleFullSKanPrism_middle_edge s hZ)).mpr
      (zeroMiddleFullSKanComparison_isInvertible s hZ)
  · have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (zeroMiddleFullSKanPrism s hZ)
        (stdSimplex.obj₀Equiv.symm (2 : Fin 3))).edge =
      (Truncated.Edge.id (X := (truncation 2).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
        ((zeroMiddleFullSKanTetrahedron s hZ).app (Opposite.op ⦋0⦌)
          (stdSimplex.obj₀Equiv.symm (3 : Fin 4)))).edge := by
      change (zeroMiddleFullSKanTetrahedron s hZ).app (Opposite.op ⦋1⦌) _ =
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.σ 0 ((zeroMiddleFullSKanTetrahedron s hZ).app (Opposite.op ⦋0⦌) _)
      rw [← σ_naturality_apply]
      congr 1 <;> (apply SSet.stdSimplex.ext; intro i; fin_cases i <;> rfl)
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr
    change IsIso (Truncated.HomotopyCategory.homMk (Truncated.Edge.id _))
    rw [Truncated.HomotopyCategory.homMk_id]
    infer_instance

/-- 同じ元の全三角柱の辺そのものが可逆である。 -/
theorem zeroMiddleFullSKanPrism_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (zeroMiddleFullSKanPrism s hZ)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorEdgeOfSimplicialHomotopy_isInvertible_of_pointwise _
    (zeroMiddleFullSKanPrism_pointwise s hZ)

/-- 元の全二胞体を厳密端面に持つ、同じ実三角柱からの全関手同型。 -/
def zeroMiddleFullSKanPrismIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (zeroMiddleFullSKanTransportedTriangle s hZ)
      (SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap stableCoreSingleKanEnrichedFunctor).app
        (Opposite.op ⦋2⦌) s)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy _ (zeroMiddleFullSKanPrism_pointwise s hZ)

end SerrePositivity.KST.Fibration
