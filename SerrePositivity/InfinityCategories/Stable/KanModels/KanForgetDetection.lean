module
public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.SimplicialNerve
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy
public import SerrePositivity.InfinityCategories.Core.InnerFiber
public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Core.LeftFiberKan
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Categories.PointedSpaces
public import SerrePositivity.InfinityCategories.F1.Coherent.Edges
public import SerrePositivity.InfinityCategories.F1.Coherent.Vertices
public import SerrePositivity.InfinityCategories.F1.Fibrations.CartesianFibration
public import SerrePositivity.InfinityCategories.F1.Transport.EdgeTransport
public import SerrePositivity.InfinityCategories.F1.Transport.InvertibleLeftTransport
public import SerrePositivity.InfinityCategories.F1.Transport.UniversalTransportReflection
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanWhiteheadComparison
public import SerrePositivity.InfinityCategories.Kan.HomotopyIsomorphism

/-!
分割で生成：docstring を書き直すこと
 # 基点を忘れた同じ coherent 辺の可逆性は、元の点つき辺へ反映される
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.InfinityCategories.HomotopyLimits
namespace SerrePositivity.KST.Fibration

/-- 元の Kan 射の coherent な可逆性は、同じ射の全基点 π 同値性を与える。 -/
theorem kanMap_piIsomorphism_of_invertible {X Y : KanObject.{u}} (f : X ⟶ Y)
    (hf : IsInvertibleEdge (coherentNerveEdge f)) : Spectra.KanPiIsomorphism f := by
  have ht := edgeTransport_isQCatEquivalence_of_isInvertibleEdge
    pointedSpaceProjection (coherentNerveEdge f) hf
  have he := (pointedSpaceTransport_coherentEdge_isQCatEquivalence_iff f).mp ht
  exact kanPiIsomorphism_of_homotopyEquivalence f he.isSimplicialHomotopyEquivalence

end SerrePositivity.KST.Fibration
