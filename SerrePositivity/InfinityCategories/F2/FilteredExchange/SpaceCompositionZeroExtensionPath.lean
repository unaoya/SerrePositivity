module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceCompositionZeroPointedProjection
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceCompositionZeroPointedInitial
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceCompositionTetrahedronZeroComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeFixedExtensionCurry

/-!
概要：零面の全係数実円柱を元の図式・初点固定の相対延長空間の区間へ入れる。
方針：元の円柱の射影・初点固定の厳密な式を同じ curry へ入力する。
規約：既存の指定比較と同じ可縮空間を使い、円柱を選び直さない。
使われ方：元の指定比較の値と実円柱の端点作用の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable (s : SpaceInfinity.{u} _⦋2⦌)
local notation "K" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))
local notation "A" => spaceSimplexPointedCoefficients s
local notation "M" => coherentSimplexMaximalization s
local notation "b" => fst Δ[2] A ≫ SSet.yonedaEquiv.symm M
local notation "i" => scaffoldFirstVertex 2 ▷ A
local notation "v" => snd Δ[0] A ≫ pointedCoherentFiberComparison K ≫
  vertexFiberι pointedSpaceProjection (coherentNerveVertex K)

/-- 元の全係数円柱が定める、同じ初点固定延長空間内の実区間。 -/
def spaceCompositionZeroExtensionPath :
    (Δ[1] : SSet.{u + 1}) ⟶ spaceSimplexPointedFamilyExtensionSpace M :=
  relativeFixedExtensionCurry pointedSpaceProjection b i v
    (spaceSimplexPointedFamily_boundary M) (spaceCompositionZeroPointedHomotopy s).h
    (spaceCompositionZeroPointedHomotopy_projection s)
    (spaceCompositionZeroPointedHomotopy_initial s)

/-- 元の可縮空間の区間を展開すると同じ全係数の実円柱そのものを回収する。 -/
lemma spaceCompositionZeroExtensionPath_uncurry :
    relativeFunctorUncurry (spaceCompositionZeroExtensionPath s ≫
      relativeFunctorExtensionSpaceι pointedSpaceProjection b i v
        (spaceSimplexPointedFamily_boundary M)) = (spaceCompositionZeroPointedHomotopy s).h :=
  relativeFixedExtensionCurry_uncurry pointedSpaceProjection b i v
    (spaceSimplexPointedFamily_boundary M) (spaceCompositionZeroPointedHomotopy s).h
    (spaceCompositionZeroPointedHomotopy_projection s)
    (spaceCompositionZeroPointedHomotopy_initial s)

end SerrePositivity.InfinityCategories.F2
