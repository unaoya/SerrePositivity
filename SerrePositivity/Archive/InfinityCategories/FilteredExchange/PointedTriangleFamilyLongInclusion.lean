module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedTriangleFamilyLongWitness
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorExtensionEndpoint

/-!
概要：長辺制限で初期値を忘れると、元の全関手の同じ長辺への相対制限になる。
方針：元の相対延長制限の包含を展開して同じ全実延長を回収する。
規約：全パラメータを保持。使われ方：長辺比較の終点像を元の全族比較へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B K : SSet.{u + 1}} {p : E ⟶ B}
  (D : PointedTransportPrismFamily (K := K) (scaffoldFirstVertex 2) p)
local notation "b" => ((Δ[2] ◁ p) ▷ K) ≫ PointedTransportPrismFamily.diagram D
local notation "b₂" => Iso.inv (α_ Δ[2] E K) ≫ b
local notation "v₂" => Iso.inv (α_ Δ[0] E K) ≫ PointedTransportPrismFamily.boundary D
local notation "hv" => triangleLongPrism_initial pointedSpaceProjection b₂ v₂
  (pointedTriangleFamily_reassociated_initial D)

/-- 長辺の始点固定の選択空間から、その同じ長辺の相対関手空間への包含。 -/
def pointedTriangleFamilyLongInclusion :
    pointedTriangleFamilyLongChoice D ⟶ relativeFunctorSpace pointedSpaceProjection
      ((stdSimplex.δ (1 : Fin 3) ▷ (E ⊗ K)) ≫ b₂) :=
  relativeFunctorExtensionSpaceι pointedSpaceProjection _ (prismEndpoint 0 (E ⊗ K))
    (simplexPrismVertex 0 0 (E ⊗ K) ≫ v₂) hv

/-- 同じ長辺の制限と包含は、元の全延長の長辺への相対制限そのもの。 -/
lemma pointedTriangleFamilyLongRestriction_ι :
    pointedTriangleFamilyLongRestriction D ≫ pointedTriangleFamilyLongInclusion D =
    relativeFunctorExtensionSpaceι pointedSpaceProjection b
      ((scaffoldFirstVertex 2 ▷ E) ▷ K) D.boundary D.projection ≫
      relativeFunctorPre pointedSpaceProjection b
        ((stdSimplex.δ (1 : Fin 3) ▷ (E ⊗ K)) ≫ (α_ Δ[2] E K).inv) := rfl

/-- 実証拠の長辺制限の頂点は、同じ実長辺と同じ実終点を保持する証拠の頂点。 -/
lemma pointedTriangleFamilyLongRestriction_point
    (W : (Δ[2] ⊗ E) ⊗ K ⟶ PointedSpaceInfinity.{u})
    (hb : ((scaffoldFirstVertex 2 ▷ E) ▷ K) ≫ W = D.boundary)
    (hp : W ≫ pointedSpaceProjection = b)
    {Q : SSet.{u + 1}} (q : Q ⟶ SpaceInfinity.{u}) (a : E ⊗ K ⟶ Q)
    (g : E ⊗ K ⟶ pullback pointedSpaceProjection q)
    (hg : g ≫ pullback.snd pointedSpaceProjection q = a)
    (ht : (simplexPrismVertex 2 2 E ▷ K) ≫ W = g ≫ pullback.fst pointedSpaceProjection q) :
    (pointedTriangleFamilyLongRestriction D).app (Opposite.op ⦋0⦌)
      (pointedPrismFamilyFixedChoice_vertex D W hb hp) =
    (pointedTriangleFamilyLongEndpointWitness D W hb hp q a g hg ht).point hv := rfl

end SerrePositivity.InfinityCategories.F2
