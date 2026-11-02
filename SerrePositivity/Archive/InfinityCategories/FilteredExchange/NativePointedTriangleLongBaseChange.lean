module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.NativePointedTriangleLongComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionBaseIso

/-!
概要：指定 native 三角形の長辺比較と底移送を、一般の始点族上で同時に構成する。
方針：元の指定比較を長辺へ制限してから、底だけの等式による同型へ写す。
規約：始点も指定比較も保持。使われ方：大きい具体的な fiber 表示の型展開を抑える。
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
  (k : K _⦋1⦌) (q : (Δ[1] : SSet.{u + 1}) ⊗ A ⟶ SpaceInfinity.{u})
  (hq : s ≫ pointedSpaceProjection = prismEndpoint 0 A ≫ q)
  (he : (stdSimplex.δ (1 : Fin 3) ▷ A) ≫ fst Δ[2] A ≫
    SSet.yonedaEquiv.symm (nativeConeTriangle c k) = q)
local notation "D" => SSet.yonedaEquiv.symm (nativeConeTriangle c k)
local notation "h₀" => triangleLongPrism_initial pointedSpaceProjection
  (fst Δ[2] A ≫ D) (snd Δ[0] A ≫ s) (nativePointedConeTriangle_initial c s hs k)

local notation "R" => triangleLongPrismExtensionRestriction pointedSpaceProjection
  (fst Δ[2] A ≫ D) (snd Δ[0] A ≫ s) (nativePointedConeTriangle_initial c s hs k)
local notation "e" => relativeExtensionBaseIso pointedSpaceProjection
  ((stdSimplex.δ (1 : Fin 3) ▷ A) ≫ fst Δ[2] A ≫ D) q (prismEndpoint 0 A) s h₀ hq he
local notation "n" => nativePointedTriangleExtensionVertex c s hs k
  (nativePointedConeTriangleLift c s hs k) (nativePointedConeTriangleLift_projection c s hs k)
  (nativePointedConeTriangleLift_initial c s hs k)

/-- 底移送後の共通空間内の、同じ全錐の長辺の実頂点。 -/
def nativePointedTriangleLongBaseChangeSource :
    (relativeFunctorExtensionSpace pointedSpaceProjection q (prismEndpoint 0 A) s hq) _⦋0⦌ :=
  (e).hom.app (Opposite.op ⦋0⦌) ((R).app (Opposite.op ⦋0⦌) n)

/-- 底移送後も、始点頂点は元の全錐の同じ実円柱を表す。 -/
lemma nativePointedTriangleLongBaseChangeSource_value :
    (nativePointedTriangleLongBaseChangeSource c s hs k q hq he).val.val =
      functorVertex ((stdSimplex.δ (1 : Fin 3) ▷ A) ≫ nativePointedConeTriangleLift c s hs k) :=
  nativePointedTriangleLongComparison_source_value c s hs k

/-- 元の三角形の長辺の実頂点を共通の底で表す。 -/
def nativePointedTriangleLongBaseChangeTarget
    (H : (Δ[2] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u})
    (hH : H ≫ pointedSpaceProjection = fst Δ[2] A ≫ D)
    (hH₀ : (scaffoldFirstVertex 2 ▷ A) ≫ H = snd Δ[0] A ≫ s) :
    (relativeFunctorExtensionSpace pointedSpaceProjection q (prismEndpoint 0 A) s hq) _⦋0⦌ :=
  (e).hom.app (Opposite.op ⦋0⦌) ((R).app (Opposite.op ⦋0⦌)
    (nativePointedTriangleExtensionVertex c s hs k H hH hH₀))

/-- 元の長辺の全円柱は共通の底への移送後も変わらない。 -/
lemma nativePointedTriangleLongBaseChangeTarget_value
    (H : (Δ[2] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u})
    (hH : H ≫ pointedSpaceProjection = fst Δ[2] A ≫ D)
    (hH₀ : (scaffoldFirstVertex 2 ▷ A) ≫ H = snd Δ[0] A ≫ s) :
    (nativePointedTriangleLongBaseChangeTarget c s hs k q hq he H hH hH₀).val.val =
      functorVertex ((stdSimplex.δ (1 : Fin 3) ▷ A) ≫ H) :=
  nativePointedTriangleLongComparison_target_value c s hs k H hH hH₀

/-- 指定比較の長辺像を、底の同じ等式で指定した共通空間へ移す。 -/
def nativePointedTriangleLongBaseChangeComparison
    (H : (Δ[2] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u})
    (hH : H ≫ pointedSpaceProjection = fst Δ[2] A ≫ D)
    (hH₀ : (scaffoldFirstVertex 2 ▷ A) ≫ H = snd Δ[0] A ≫ s) :
    VertexIso (nativePointedTriangleLongBaseChangeSource c s hs k q hq he)
      (nativePointedTriangleLongBaseChangeTarget c s hs k q hq he H hH hH₀) :=
  relativeExtensionBaseIso_map pointedSpaceProjection
    ((stdSimplex.δ (1 : Fin 3) ▷ A) ≫ fst Δ[2] A ≫ D) q (prismEndpoint 0 A) s h₀ hq he
    (nativePointedTriangleLongComparisonIso c s hs k H hH hH₀)

end SerrePositivity.InfinityCategories.F2
