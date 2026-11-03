module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpacePrefixConeCosliceHomotopy
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCompositionTetrahedronMaximalization

/-!
概要：零面の元の実 coslice 族と標準族を結ぶ、指定 prefix 円柱。
方針：三単体の最大化を元の最大化三角形の初点退化へ戻す。
規約：実円柱は prefix 変形そのもの、両端だけを厳密に同定する。
使われ方：全族比較の終点像を元の精密化へ同定する。
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
variable (s : SpaceInfinity.{u} _⦋2⦌)
local notation "K" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))
local notation "Z" => sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex K))
local notation "T" => coherentCompositionTetrahedron s
local notation "M" => coherentSimplexMaximalization s

/-- 最大化した比較三単体の零面の coslice 点は元の標準の初点 cone。 -/
lemma spaceCompositionTetrahedron_maximal_coslice_zero :
    SimplicialObject.δ Z 0 (spaceSimplexSourceCone (coherentSimplexMaximalization T)) =
      spaceSimplexSourceCone M := by
  apply spaceCosliceSourceSimplex_injective K 2
  exact (spaceSimplexSourceCone_zero_face_coordinates
    (coherentSimplexMaximalization T)).trans
      ((coherentCompositionTetrahedron_maximalization s).trans
        ((coherentConeTailExtension_eq_sigmaZero M).symm.trans
          (spaceSimplexSourceCone_coordinates M).symm))

/-- 最大化三角形の標準 coslice 族から元の零面の実族への指定円柱。 -/
def spaceCompositionTetrahedronZeroCosliceHomotopy :
    SSet.Homotopy (SSet.yonedaEquiv.symm (spaceSimplexSourceCone M))
      (SSet.yonedaEquiv.symm (SimplicialObject.δ Z 0 (spaceSimplexSourceCone T))) where
  h := (spacePrefixConeCosliceHomotopy T).h
  h₀ := (spacePrefixConeCosliceHomotopy T).h₀.trans
    (congrArg SSet.yonedaEquiv.symm (spaceCompositionTetrahedron_maximal_coslice_zero s))
  h₁ := (spacePrefixConeCosliceHomotopy T).h₁
  rel := (spacePrefixConeCosliceHomotopy T).rel

end SerrePositivity.InfinityCategories.F2
