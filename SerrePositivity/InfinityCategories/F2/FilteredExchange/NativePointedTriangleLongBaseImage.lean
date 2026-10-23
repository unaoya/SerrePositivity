module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.NativePointedTriangleLongBaseChange

/-!
概要：長辺制限と共通底移送の指定像の後合成を、元の全三角形比較の単一の像へ戻す。
方針：一般の全始点族でホモトピー圏の合成則を証明してから、具体的な fiber に適用する。
規約：元の指定比較を保持。使われ方：大きい具体的な native 比較の型検査の抽象化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {K A Z : SSet.{u + 1}} {d : K ⟶ SpaceInfinity.{u}} (c : JoinCone d)
  (s : A ⟶ PointedSpaceInfinity.{u}) (hs : s ≫ pointedSpaceProjection = SSet.const c.vertex)
  (k : K _⦋1⦌) (q : (Δ[1] : SSet.{u + 1}) ⊗ A ⟶ SpaceInfinity.{u})
  (hq : s ≫ pointedSpaceProjection = prismEndpoint 0 A ≫ q)
  (he : (stdSimplex.δ (1 : Fin 3) ▷ A) ≫ fst Δ[2] A ≫
    SSet.yonedaEquiv.symm (nativeConeTriangle c k) = q)
local notation "D" => SSet.yonedaEquiv.symm (nativeConeTriangle c k)
local notation "R" => triangleLongPrismExtensionRestriction pointedSpaceProjection
  (fst Δ[2] A ≫ D) (snd Δ[0] A ≫ s) (nativePointedConeTriangle_initial c s hs k)
local notation "h₀" => triangleLongPrism_initial pointedSpaceProjection
  (fst Δ[2] A ≫ D) (snd Δ[0] A ≫ s) (nativePointedConeTriangle_initial c s hs k)
local notation "E" => relativeExtensionBaseIso pointedSpaceProjection
  ((stdSimplex.δ (1 : Fin 3) ▷ A) ≫ fst Δ[2] A ≫ D) q (prismEndpoint 0 A) s h₀ hq he

/-- 長辺・底移送・後合成による指定像は、同じ全三角形比較の合成写像による像である。 -/
lemma nativePointedTriangleLongBaseChangeComparison_post_map
    (H : (Δ[2] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u})
    (hH : H ≫ pointedSpaceProjection = fst Δ[2] A ≫ D)
    (hH₀ : (scaffoldFirstVertex 2 ▷ A) ≫ H = snd Δ[0] A ≫ s)
    (f : relativeFunctorExtensionSpace pointedSpaceProjection q (prismEndpoint 0 A) s hq ⟶ Z) :
    VertexIso.map (nativePointedTriangleLongBaseChangeComparison c s hs k q hq he H hH hH₀) f =
      VertexIso.map (nativePointedTriangleComparisonIso c s hs k H hH hH₀)
        (R ≫ (E).hom ≫ f) := by
  change VertexIso.map (VertexIso.map (VertexIso.map
    (nativePointedTriangleComparisonIso c s hs k H hH hH₀) R) (E).hom) f = _
  rw [vertexIso_map_comp, vertexIso_map_comp]

end SerrePositivity.InfinityCategories.F2
