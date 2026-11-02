module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedPrismFamilyComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionRestriction

/-!
概要：全パラメータ固定の pointed 三角形の選択を、同じ全係数を持つ三角形へ移す。
方針：積の結合子の厳密な初期正方形に相対延長の制限を適用する。
規約：全底・全初期値・実延長を保持。使われ方：既存の長辺 prism 制限の再利用。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 結合子を移しても、元の最初の頂点を含む正方形は全パラメータで厳密に可換。 -/
lemma pointedTriangleFamily_initial_associator (E K : SSet.{u + 1}) :
    (scaffoldFirstVertex 2 ▷ (E ⊗ K)) ≫ (α_ (Δ[2] : SSet.{u + 1}) E K).inv =
      (α_ (Δ[0] : SSet.{u + 1}) E K).inv ≫ ((scaffoldFirstVertex 2 ▷ E) ▷ K) := by
  apply SSet.hom_ext
  intro n
  rfl

variable {E B K : SSet.{u + 1}} {p : E ⟶ B}
  (D : PointedTransportPrismFamily (K := K) (scaffoldFirstVertex 2) p)
local notation "b₂" => ((Δ[2] ◁ p) ▷ K) ≫ PointedTransportPrismFamily.diagram D

/-- 元の初期値と底を結合子で移した後も、同じ全初期値の条件を厳密に保つ。 -/
lemma pointedTriangleFamily_reassociated_initial :
    ((α_ (Δ[0] : SSet.{u + 1}) E K).inv ≫ D.boundary) ≫ pointedSpaceProjection =
      (scaffoldFirstVertex 2 ▷ (E ⊗ K)) ≫ ((α_ Δ[2] E K).inv ≫ b₂) := by
  rw [Category.assoc, D.projection, ← Category.assoc,
    ← pointedTriangleFamily_initial_associator, Category.assoc]

/-- 元の全延長を、全係数 E⊗K の同じ全三角形の選択空間へ移す実際の射。 -/
def pointedTriangleFamilyReassociate :
    pointedPrismFamilyFixedChoice D ⟶
      relativeFunctorExtensionSpace pointedSpaceProjection ((α_ Δ[2] E K).inv ≫ b₂)
        (scaffoldFirstVertex 2 ▷ (E ⊗ K)) ((α_ Δ[0] E K).inv ≫ D.boundary)
        (pointedTriangleFamily_reassociated_initial D) :=
  relativeExtensionRestriction pointedSpaceProjection b₂ ((scaffoldFirstVertex 2 ▷ E) ▷ K)
    D.boundary D.projection (α_ Δ[2] E K).inv (α_ Δ[0] E K).inv
    (scaffoldFirstVertex 2 ▷ (E ⊗ K)) (pointedTriangleFamily_initial_associator E K)

end SerrePositivity.InfinityCategories.F2
