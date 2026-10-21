module

public import SerrePositivity.InfinityCategories.F2.PointedTriangleFamilyLongInclusion
public import SerrePositivity.InfinityCategories.F2.RelativeFunctorRestrictedEndpoint

/-!
概要：結合子で移した同じ長辺の指定終点評価は、元の全三角形の指定終点評価に一致する。
方針：実延長の包含の一致と相対前合成の合成則を使う。
規約：底の表示変更と指定比較の値を保持。使われ方：三証拠の比較を native 比較へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B K Q : SSet.{u + 1}} {p : E ⟶ B}
  (D : PointedTransportPrismFamily (K := K) (scaffoldFirstVertex 2) p)
  (q : Q ⟶ SpaceInfinity.{u}) (a : E ⊗ K ⟶ Q)
local notation "b" => ((Δ[2] ◁ p) ▷ K) ≫ PointedTransportPrismFamily.diagram D
local notation "b₂" => Iso.inv (α_ Δ[2] E K) ≫ b
local notation "v₂" => Iso.inv (α_ Δ[0] E K) ≫ PointedTransportPrismFamily.boundary D
local notation "hv" => triangleLongPrism_initial pointedSpaceProjection b₂ v₂
  (pointedTriangleFamily_reassociated_initial D)
local notation "h₁" => (stdSimplex.δ (1 : Fin 3) ▷ (E ⊗ K)) ≫ Iso.inv (α_ Δ[2] E K)
variable (hEnd : (simplexPrismVertex 2 2 E ▷ K) ≫ ((Δ[2] ◁ p) ▷ K) ≫ D.diagram = a ≫ q)

include hEnd in
/-- 移した元の長辺の底の終点も、元の全三角形の同じ終点の底そのもの。 -/
lemma pointedTriangleFamilyLong_base_endpoint :
    prismEndpoint 1 (E ⊗ K) ≫ (h₁ ≫ b) = a ≫ q := hEnd

/-- 同じ始点固定の長辺の全選択を、元の指定終点の標的の全空間へ評価する。 -/
def pointedTriangleFamilyLongEndpointMap :
    pointedTriangleFamilyLongChoice D ⟶
      relativeFunctorSpace (pullback.snd pointedSpaceProjection q) a :=
  relativeFunctorExtensionEndpoint pointedSpaceProjection (h₁ ≫ b)
    (prismEndpoint 0 (E ⊗ K)) (simplexPrismVertex 0 0 (E ⊗ K) ≫ v₂) hv
    (prismEndpoint 1 (E ⊗ K)) q a (pointedTriangleFamilyLong_base_endpoint D q a hEnd)

/-- 長辺への実制限を経る指定終点評価は、元の全三角形の同じ指定終点評価。 -/
lemma pointedTriangleFamilyLongEndpoint_factor :
    pointedTriangleFamilyLongRestriction D ≫ pointedTriangleFamilyLongEndpointMap D q a hEnd =
    relativeFunctorExtensionEndpoint pointedSpaceProjection b
      ((scaffoldFirstVertex 2 ▷ E) ▷ K) D.boundary D.projection
      (simplexPrismVertex 2 2 E ▷ K) q a hEnd := by
  unfold pointedTriangleFamilyLongEndpointMap
  rw [← relativeFunctorExtensionEndpoint_factor, ← Category.assoc]
  change (pointedTriangleFamilyLongRestriction D ≫ pointedTriangleFamilyLongInclusion D) ≫
    relativeFunctorRestrictedEndpoint pointedSpaceProjection (h₁ ≫ b)
      (prismEndpoint 1 (E ⊗ K)) q a _ = _
  rw [pointedTriangleFamilyLongRestriction_ι, Category.assoc, relativeFunctorRestrictedEndpoint_pre]
  change relativeFunctorExtensionSpaceι pointedSpaceProjection b
      ((scaffoldFirstVertex 2 ▷ E) ▷ K) D.boundary D.projection ≫
      relativeFunctorRestrictedEndpoint pointedSpaceProjection b
        (prismEndpoint 1 (E ⊗ K) ≫ h₁) q a _ =
    relativeFunctorExtensionSpaceι pointedSpaceProjection b
      ((scaffoldFirstVertex 2 ▷ E) ▷ K) D.boundary D.projection ≫
      relativeFunctorRestrictedEndpoint pointedSpaceProjection b
        (simplexPrismVertex 2 2 E ▷ K) q a hEnd
  apply congrArg (fun z => relativeFunctorExtensionSpaceι pointedSpaceProjection b
    ((scaffoldFirstVertex 2 ▷ E) ▷ K) D.boundary D.projection ≫ z)
  exact relativeFunctorRestrictedEndpoint_congr pointedSpaceProjection b q a rfl hEnd hEnd

end SerrePositivity.InfinityCategories.F2
