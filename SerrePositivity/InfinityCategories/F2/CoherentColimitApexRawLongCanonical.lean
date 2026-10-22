module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitApexRawEdgeValues
public import SerrePositivity.InfinityCategories.F2.CoherentColimitApexCoefficientMap
public import SerrePositivity.InfinityCategories.F2.PointedEdgeValueCanonicalPresentation

/-!
概要：元の raw 長辺の値比較を、同じ canonical 比較の標準初期係数への前合成へ戻す。
方針：元の実辺の表示変更を保ち、初期係数の fiber 移送を実包含で照合する。
規約：元の長辺・初期値・指定比較を保持。使われ方：元の長辺評価比較の二因子の回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "s" => coherentColimitApexTriangle B T
local notation "K₀" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))
local notation "f" => coherentEdgeHom (SpaceInfinity.δ 1 s)
local notation "q" => coherentColimitApexCoefficientMap B T
local notation "h₀" => coherentColimitApex_raw_zero_vertex B T
local notation "C" => pointedCoherentFiberComparison K₀ ≫
  eqToHom (congrArg (vertexFiber pointedSpaceProjection)
    (Eq.symm (spaceInfinityVertex_eq_coherent K₀)))

/-- 元の初期係数を標準 fiber へ移すと、元の coherent 初期比較の同じ標準表示となる。 -/
lemma coherentColimitApexCoefficientMap_standard :
    q ≫ eqToHom (congrArg (vertexFiber pointedSpaceProjection) h₀) = C := by
  apply (cancel_mono (vertexFiberι pointedSpaceProjection (spaceInfinityVertex K₀))).mp
  rw [Category.assoc, vertexFiberTransport_ι pointedSpaceProjection h₀,
    coherentColimitApexCoefficientMap_ι, Category.assoc,
    vertexFiberTransport_ι pointedSpaceProjection (spaceInfinityVertex_eq_coherent K₀).symm]

/-- 元の raw 長辺値比較は、同じ canonical 比較の同じ移送初期係数での前合成。 -/
lemma coherentColimitApexRawLongValueIso_precomp_heq_canonical :
    HEq ((coherentColimitApexRawLongValueIso B T).precomp q)
      ((pointedValueMorphismIntervalIso f).precomp
        (q ≫ eqToHom (congrArg (vertexFiber pointedSpaceProjection) h₀))) :=
  pointedSpaceMorphismEdgeValueIso_precomp_heq_canonical f
    (coherentColimitRawSpaceEdge B d) h₀ (coherentColimitApex_raw_two_vertex B T)
    ((coherentColimitRawSpaceEdge_long B a T).trans
      (pointedRightMorphismEdge_recover (SpaceInfinity.δ 1 s)).symm) q

/-- 元の raw 長辺値比較は、同じ canonical 比較の元の標準 coherent 初期係数での値。 -/
lemma coherentColimitApexRawLongValueIso_precomp_heq_standard :
    HEq ((coherentColimitApexRawLongValueIso B T).precomp q)
      ((pointedValueMorphismIntervalIso f).precomp C) := by
  exact (coherentColimitApexRawLongValueIso_precomp_heq_canonical B T).trans
    (functorIso_precomp_heq_of_map_eq (pointedValueMorphismIntervalIso f)
      (coherentColimitApexCoefficientMap_standard B T))

end SerrePositivity.InfinityCategories.F2
