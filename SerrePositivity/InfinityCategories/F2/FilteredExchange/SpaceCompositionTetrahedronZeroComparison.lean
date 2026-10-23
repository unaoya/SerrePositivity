module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceCompositionTetrahedronZeroFamily
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceSimplexPointedFamilyComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceSimplexPointedRestrictionInitial

/-!
概要：同じ最大化図式と元の全初点を固定して、零面の実族を標準族と比較する。
方針：零面の図式・始点の厳密な式で元の可縮な延長空間へ入力する。
規約：零面の族を置き換えず、同じ全比較の制限を使う。
使われ方：長辺の指定精密化と厳密合成側を比較する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable (s : SpaceInfinity.{u} _⦋2⦌)
local notation "A" => spaceSimplexPointedCoefficients s
local notation "M" => coherentSimplexMaximalization s
local notation "L" => spaceCompositionTetrahedronZeroFamily s
local notation "b" => fst Δ[2] A ≫ SSet.yonedaEquiv.symm M
local notation "i" => scaffoldFirstVertex 2 ▷ A
local notation "K" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))
local notation "v" => snd Δ[0] A ≫ pointedCoherentFiberComparison K ≫
  vertexFiberι pointedSpaceProjection (coherentNerveVertex K)

/-- 元の零面の実族を同じ図式・初点固定の延長空間に入れた頂点。 -/
def spaceCompositionTetrahedronZeroExtensionVertex :
    (spaceSimplexPointedFamilyExtensionSpace M) _⦋0⦌ :=
  relativeFunctorExtensionSpaceVertexEquiv pointedSpaceProjection b i v
    (spaceSimplexPointedFamily_boundary M)
      ⟨L, spaceCompositionTetrahedronZeroFamily_projection s,
        spaceCompositionTetrahedronZeroFamily_initial s⟩

/-- 同じ全図式・全初点を保つ標準族から元の零面の族への指定比較。 -/
def spaceCompositionTetrahedronZeroComparison :
    VertexIso (spaceSimplexPointedFamilyExtensionVertex M)
      (spaceCompositionTetrahedronZeroExtensionVertex s) :=
  spaceSimplexPointedFamilyComparisonIso M L
    (spaceCompositionTetrahedronZeroFamily_projection s)
    (spaceCompositionTetrahedronZeroFamily_initial s)

/-- 零面の部分図式への比較も同じ全比較の指定像として定義する。 -/
def spaceCompositionTetrahedronZeroRestrictionIso
    {C : SSet.{u + 1}} (r : C ⟶ (Δ[2] : SSet.{u + 1}) ⊗ A) :=
  spaceSimplexPointedFamilyRestrictionIso M L
    (spaceCompositionTetrahedronZeroFamily_projection s)
    (spaceCompositionTetrahedronZeroFamily_initial s) r

/-- 同じ全比較の始点制限は元の全初点族の恒等同型。 -/
lemma spaceCompositionTetrahedronZeroRestrictionIso_initial :
    HEq (spaceCompositionTetrahedronZeroRestrictionIso s i)
      (Iso.refl (SSet.HomotopyCategory.mk
        (relativeFunctorVertex pointedSpaceProjection (i ≫ b) v
          (spaceSimplexPointedFamily_boundary M)))) :=
  spaceSimplexPointedFamilyRestrictionIso_initial M L
    (spaceCompositionTetrahedronZeroFamily_projection s)
    (spaceCompositionTetrahedronZeroFamily_initial s)

end SerrePositivity.InfinityCategories.F2
