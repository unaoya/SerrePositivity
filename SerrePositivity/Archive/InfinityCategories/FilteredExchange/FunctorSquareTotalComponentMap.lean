module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorSquareTotalComponent
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativeFunctorCurryIsoPresentation
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.VertexIsoCompositionTransport
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorHomotopyRelativePost

/-!
概要：元の二面の全空間成分の指定値の回収を、その後の同じ射の像にも保持する。
方針：同じ両端の相対頂点と全空間成分の値の一致を使う。
規約：同じ全二面を保持。使われ方：元の値への射影と native な二面比較の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u + 1}} {F G L J : B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {v : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  {s : SSet.Homotopy F L} {w : SSet.Homotopy L J}
  (U : FunctorCompositionTriangle a v d) (D : FunctorCompositionTriangle s w d)
local notation "p" => leftUnstraighteningProjection F
local notation "x" => relativeFunctorVertex p p (𝟙 (leftUnstraightening F)) (Category.id_comp p)
local notation "eD" => FunctorIso.app (functorTriangleSequentialPostComparison D p) x
local notation "eU" => FunctorIso.app (functorTriangleSequentialPostComparison U p) x
local notation "rD" => functorTriangleRelativeComparison D
local notation "rU" => functorTriangleRelativeComparison U

/-- 元の全空間の二面比較成分の像は、同じ元の相対二面比較の像と値まで一致する。 -/
lemma functorSquareComparison_total_app_map_heq {V : SSet.{u + 1}}
    (q : relativeFunctorSpace (leftUnstraighteningProjection J) p ⟶ V) :
    HEq (VertexIso.map ((eD).symm ≪≫ eU) q)
      (VertexIso.map ((rD).symm ≪≫ rU) q) := by
  have hDt : ((functorHomotopyRelativePost w p).app _
      ((functorHomotopyRelativePost s p).app _ x)) =
      relativeFunctorVertex (leftUnstraighteningProjection J) p
        ((leftUnstraighteningMappingVertexMap F L (coherentVertexOfHomotopy s)).val ≫
          (leftUnstraighteningMappingVertexMap L J (coherentVertexOfHomotopy w)).val)
        (by rw [Category.assoc,
          (leftUnstraighteningMappingVertexMap L J (coherentVertexOfHomotopy w)).property,
          (leftUnstraighteningMappingVertexMap F L (coherentVertexOfHomotopy s)).property]) := by
    apply Subtype.ext
    rfl
  have hUt : ((functorHomotopyRelativePost v p).app _
      ((functorHomotopyRelativePost a p).app _ x)) =
      relativeFunctorVertex (leftUnstraighteningProjection J) p
        ((leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy a)).val ≫
          (leftUnstraighteningMappingVertexMap G J (coherentVertexOfHomotopy v)).val)
        (by rw [Category.assoc,
          (leftUnstraighteningMappingVertexMap G J (coherentVertexOfHomotopy v)).property,
          (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy a)).property]) := by
    apply Subtype.ext
    rfl
  exact vertexIso_map_heq_of_heq _ _ hDt hUt
    (functorSquareComparison_total_app_heq U D) q

end SerrePositivity.InfinityCategories.F2
