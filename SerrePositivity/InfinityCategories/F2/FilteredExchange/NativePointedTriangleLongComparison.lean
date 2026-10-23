module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.NativePointedTriangleComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.TriangleLongPrismRestriction

/-!
概要：全錐と元の三角形の指定比較を、同じ長辺 prism の指定比較へ制限する。
方針：始点固定の相対延長の制限と可縮な長辺延長空間の指定同型の一意性を使う。
規約：指定値と元の全円柱を保持。使われ方：実際の fiber 比較と native な全錐の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {K A : SSet.{u + 1}} {d : K ⟶ SpaceInfinity.{u}} (c : JoinCone d)
  (s : A ⟶ PointedSpaceInfinity.{u}) (hs : s ≫ pointedSpaceProjection = SSet.const c.vertex)
  (k : K _⦋1⦌)
local notation "D" => SSet.yonedaEquiv.symm (nativeConeTriangle c k)
local notation "b" => fst Δ[2] A ≫ D
local notation "v" => snd Δ[0] A ≫ s
local notation "hv" => nativePointedConeTriangle_initial c s hs k
local notation "R" => triangleLongPrismExtensionRestriction pointedSpaceProjection b v hv
local notation "N" => nativePointedConeTriangleLift c s hs k
local notation "n" => nativePointedTriangleExtensionVertex c s hs k N
  (nativePointedConeTriangleLift_projection c s hs k)
  (nativePointedConeTriangleLift_initial c s hs k)
variable (H : (Δ[2] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u})
  (hH : H ≫ pointedSpaceProjection = fst Δ[2] A ≫
    SSet.yonedaEquiv.symm (nativeConeTriangle c k))
  (hH₀ : (scaffoldFirstVertex 2 ▷ A) ≫ H = snd Δ[0] A ≫ s)
local notation "o" => nativePointedTriangleExtensionVertex c s hs k H hH hH₀

/-- 全三角形の指定比較を同じ長辺の始点固定 prism 空間へ写した同型。 -/
def nativePointedTriangleLongComparisonIso :=
  VertexIso.map (nativePointedTriangleComparisonIso c s hs k H hH hH₀) R

/-- この像は、同じ二つの長辺円柱を比較する可縮な延長空間の指定値に等しい。 -/
lemma nativePointedTriangleLongComparisonIso_eq :
    nativePointedTriangleLongComparisonIso c s hs k H hH hH₀ =
      (triangleLongPrismExtension_contractible pointedSpaceProjection b v hv).vertexIso
        ((R).app (Opposite.op ⦋0⦌) n) ((R).app (Opposite.op ⦋0⦌) o) :=
  triangleLongPrismExtensionRestriction_vertexIso pointedSpaceProjection b v hv
    (nativePointedTriangleComparisonIso c s hs k H hH hH₀)

/-- 比較の始点は、同じ全 native 錐から制限した長辺の実際の全円柱。 -/
lemma nativePointedTriangleLongComparison_source_value :
    (((R).app (Opposite.op ⦋0⦌) n).val).val =
      functorVertex ((stdSimplex.δ (1 : Fin 3) ▷ A) ≫ N) :=
  triangleLongPrismExtensionRestriction_vertex_value pointedSpaceProjection b v hv N
    (nativePointedConeTriangleLift_projection c s hs k)
    (nativePointedConeTriangleLift_initial c s hs k)

/-- 比較の終点は、元の全三角形の同じ長辺の実際の全円柱。 -/
lemma nativePointedTriangleLongComparison_target_value :
    (((R).app (Opposite.op ⦋0⦌) o).val).val =
      functorVertex ((stdSimplex.δ (1 : Fin 3) ▷ A) ≫ H) :=
  triangleLongPrismExtensionRestriction_vertex_value pointedSpaceProjection b v hv H hH hH₀

end SerrePositivity.InfinityCategories.F2
