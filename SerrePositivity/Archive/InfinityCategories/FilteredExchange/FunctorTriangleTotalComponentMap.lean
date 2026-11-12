module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTriangleTotalComponent
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorHomotopyRelativePost
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativeFunctorCurryIsoPresentation

/-!
概要：元の全空間の三角形比較の成分を、その後の同じ射の像へも値を保って回収する。
方針：元の両端の相対頂点と指定成分の値の保持を使う。
規約：元の三角形・指定値を保持。使われ方：単位作用の後の全三角形比較を実射へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u + 1}} {F G J : B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b c)
local notation "p" => leftUnstraighteningProjection F
local notation "x" => relativeFunctorVertex p p (𝟙 (leftUnstraightening F)) (Category.id_comp p)

/-- 全空間の元の指定成分の像は、同じ相対三角形比較の像と一致する。 -/
lemma functorTriangleSequentialPostComparison_total_app_map_heq {V : SSet.{u + 1}}
    (q : relativeFunctorSpace (leftUnstraighteningProjection J) p ⟶ V) :
    HEq (VertexIso.map ((functorTriangleSequentialPostComparison T p).app x) q)
      (VertexIso.map (functorTriangleRelativeComparison T) q) := by
  have hs : ((functorHomotopyRelativePost c p).app _ x) =
      relativeFunctorVertex (leftUnstraighteningProjection J) p
        (leftUnstraighteningMappingVertexMap F J (coherentVertexOfHomotopy c)).val
        (leftUnstraighteningMappingVertexMap F J (coherentVertexOfHomotopy c)).property := by
    apply Subtype.ext
    rfl
  have ht : ((functorHomotopyRelativePost b p).app _
      ((functorHomotopyRelativePost a p).app _ x)) =
      relativeFunctorVertex (leftUnstraighteningProjection J) p
        ((leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy a)).val ≫
          (leftUnstraighteningMappingVertexMap G J (coherentVertexOfHomotopy b)).val)
        (by rw [Category.assoc,
          (leftUnstraighteningMappingVertexMap G J (coherentVertexOfHomotopy b)).property,
          (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy a)).property]) := by
    apply Subtype.ext
    rfl
  exact vertexIso_map_heq_of_heq _ _ hs ht
    (functorTriangleSequentialPostComparison_total_app_heq T) q

end SerrePositivity.InfinityCategories.F2
