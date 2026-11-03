module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTriangleTotalComponent
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.VertexIsoCompositionTransport
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorHomotopyRelativePost

/-!
概要：全空間の恒等初期値で、共通対角を持つ二面の元の比較合成を回収する。
方針：同じ二つの指定成分の値を相対比較へ戻し、逆と合成を保持する。
規約：二面と指定対角を選び直さない。使われ方：単位正方形の全空間作用の照合。
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

/-- 原全空間の同じ初期値で、二面の指定比較合成を元の相対比較合成へ値まで戻す。 -/
lemma functorSquareComparison_total_app_heq :
    HEq ((eD).symm ≪≫ eU) ((rD).symm ≪≫ rU) := by
  have hD := functorTriangleSequentialPostComparison_total_app_heq D
  have hU := functorTriangleSequentialPostComparison_total_app_heq U
  have hDs : ((functorHomotopyRelativePost d p).app _ x) =
      relativeFunctorVertex (leftUnstraighteningProjection J) p
        (leftUnstraighteningMappingVertexMap F J (coherentVertexOfHomotopy d)).val
        (leftUnstraighteningMappingVertexMap F J (coherentVertexOfHomotopy d)).property := by
    apply Subtype.ext
    rfl
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
  exact vertexIso_trans_heq_of_heq (eD).symm eU (rD).symm rU hDt hDs hUt
    (vertexIso_symm_heq_of_heq eD rD hDs hDt hD) hU

end SerrePositivity.InfinityCategories.F2
