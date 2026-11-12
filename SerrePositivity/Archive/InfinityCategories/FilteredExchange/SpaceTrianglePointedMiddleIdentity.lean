module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceSimplexPointedFamilyEndpointWitness
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionFiberWitnessRestriction
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionFiberWitnessIdentity
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PrismLiftSpace

/-!
概要：同じ実初辺を持つ全三角形比較の指定中間像は恒等同型になる。
方針：同じ全比較を実初辺の始点固定延長空間へ制限し、同じ実 prism を消去する。
規約：元の指定値・全係数を保持。使われ方：零面の指定比較の中間像の固定。
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
local notation "p" => pointedSpaceProjection
local notation "A" => spaceSimplexPointedCoefficients s
local notation "b" => fst Δ[2] A ≫ SSet.yonedaEquiv.symm s
local notation "i" => scaffoldFirstVertex 2 ▷ A
local notation "v" => snd Δ[0] A ≫
  pointedCoherentFiberComparison (EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))) ≫
    vertexFiberι p
      (coherentNerveVertex (EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))))
local notation "j" => stdSimplex.δ (2 : Fin 3) ▷ A
local notation "k" => simplexPrismVertex 0 0 A
local notation "r" => simplexPrismVertex 2 1 A

/-- 全三角形の同じ指定中間像は、二実初辺が同じなら厳密に恒等同型。 -/
lemma spaceTrianglePointedFamilyMiddleEndpointIso_eq_refl_of_first_eq
    (L : (Δ[2] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u})
    (hL : L ≫ p = b) (hL₀ : i ≫ L = v)
    (y : SpaceInfinity.{u} _⦋0⦌) (hy : r ≫ b = SSet.const y)
    (g : A ⟶ vertexFiber p y)
    (hg : r ≫ spaceSimplexPointedFamily s = g ≫ vertexFiberι p y)
    (hg' : r ≫ L = g ≫ vertexFiberι p y)
    (hfirst : j ≫ spaceSimplexPointedFamily s = j ≫ L) :
    spaceSimplexPointedFamilyEndpointIso s L hL hL₀ r y hy g g hg hg' = Iso.refl _ := by
  have hs : prismEndpoint 0 A ≫ j = k ≫ i := by
    apply SSet.hom_ext
    intro n
    rfl
  have he : prismEndpoint 1 A ≫ j = r := by
    apply SSet.hom_ext
    intro n
    rfl
  rw [spaceSimplexPointedFamilyEndpointIso_eq_witnessIso]
  have h := relativeExtensionFiberEndpoint_witnessIso_restriction p b i
    (leftAnodyneExtensions_whiskerRight _ (scaffoldFirstVertex_leftAnodyne 2) A)
    v (spaceSimplexPointedFamily_boundary s) j k (prismEndpoint 0 A)
    (prismEndpoint_zero_leftAnodyne A) hs r (prismEndpoint 1 A) he y hy
    (spaceSimplexPointedFamily s) L (spaceSimplexPointedFamily_projection s) hL
    (spaceSimplexPointedFamily_firstVertex s) hL₀ g g hg hg'
  exact h.trans (relativeExtensionFiberEndpoint_witnessIso_eq_refl_of_eq p _ _
    (prismEndpoint_zero_leftAnodyne A) _ _ _ y _ _ _ _ _ _ _ g _ _ hfirst)

end SerrePositivity.InfinityCategories.F2
