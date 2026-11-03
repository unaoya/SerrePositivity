module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTriangleTotalComponentMap

/-!
概要：元の三角形の任意の相対始点成分を、同じ実射による前合成へ戻す。
方針：sequential 表示の終点補正と、元の相対比較の豊穣後合成の成分式を使う。
規約：元の全三角形と指定値を保持。使われ方：定値余極限三角形の単位始点での評価。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u + 1}} {F G J : B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b c) (s : C ⟶ leftUnstraightening F)
local notation "p" => s ≫ leftUnstraighteningProjection F
local notation "x" => relativeFunctorVertex (leftUnstraighteningProjection F) p s rfl
local notation "R" => relativeFunctorPre (leftUnstraighteningProjection J)
  (leftUnstraighteningProjection F) s

/-- 任意の元の始点の指定三角形成分の像は、同じ実射による元の比較の前合成の像。 -/
lemma functorTriangleSequentialPostComparison_source_app_map_heq {V : SSet.{u + 1}}
    (q : relativeFunctorSpace (leftUnstraighteningProjection J) p ⟶ V) :
    HEq (VertexIso.map ((functorTriangleSequentialPostComparison T p).app x) q)
      (VertexIso.map (VertexIso.map (functorTriangleRelativeComparison T) R) q) := by
  have h := (functorTriangleSequentialPostComparison_app_heq_post T _ x).trans
    (functorTrianglePostComparison_app_heq_pre T _ s rfl)
  have h₀ : (functorHomotopyRelativePost c (s ≫ leftUnstraighteningProjection F)).app _ x =
      (R).app _ (relativeFunctorVertex (leftUnstraighteningProjection J)
        (leftUnstraighteningProjection F)
        (leftUnstraighteningMappingVertexMap F J (coherentVertexOfHomotopy c)).val
        (leftUnstraighteningMappingVertexMap F J (coherentVertexOfHomotopy c)).property) := by
    apply Subtype.ext
    rfl
  have h₁ : (functorHomotopyRelativePost b (s ≫ leftUnstraighteningProjection F)).app _
      ((functorHomotopyRelativePost a (s ≫ leftUnstraighteningProjection F)).app _ x) =
      (R).app _ (relativeFunctorVertex (leftUnstraighteningProjection J)
        (leftUnstraighteningProjection F)
        ((leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy a)).val ≫
          (leftUnstraighteningMappingVertexMap G J (coherentVertexOfHomotopy b)).val)
        (by rw [Category.assoc,
          (leftUnstraighteningMappingVertexMap G J (coherentVertexOfHomotopy b)).property,
          (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy a)).property])) := by
    apply Subtype.ext
    rfl
  exact vertexIso_map_heq_of_heq _ _ h₀ h₁ h q

end SerrePositivity.InfinityCategories.F2
