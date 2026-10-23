module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitFirstNativeRelation
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorTetrahedronTensorReflection

/-!
概要：元の単位三単体の四面の指定比較を、元の三角形のまま厳密な合成関係へ戻す。
方針：元の外側面と同じ内部面の等式を用い、比較も三角形も再選択しない。
規約：元の三単体を保持。使われ方：四面の指定比較の可換性の具体化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d)

local notation "p" => leftUnstraighteningProjection F
local notation "x₀" => relativeFunctorVertex p p (𝟙 (leftUnstraightening F)) (Category.id_comp p)

/-- 元の同じ全空間上で、第 0 単位三単体の指定四面の比較は厳密な合成関係を満たす。 -/
lemma coherentColimitUnitFirstTotalRelation :
    (functorTriangleSequentialPostComparison (coherentColimitUnitLowerTriangle B d) p).app x₀ ≪≫
      (functorTriangleSequentialPostComparison (coherentColimitConstantTriangle B T) p).app
        ((functorHomotopyRelativePost (coconeTransformationHomotopy (coherentDiagramTotalCocone
          F)) p).app _ x₀) =
    (functorTriangleSequentialPostComparison (coherentColimitUnitInteriorFirst B T) p).app x₀ ≪≫
      VertexIso.map ((functorTriangleSequentialPostComparison (coherentColimitUnitLowerTriangle
        B l) p).app x₀)
        (functorHomotopyRelativePost (simplicialHomotopyOfFunctorEdge
          (coherentColimitConstantEdge B r)) p) :=
  functorTetrahedronPostComparison_square_of_tensor_pre
    (coherentColimitUnitLowerTriangle B l) (coherentColimitConstantTriangle B T)
    (coherentColimitUnitLowerTriangle B d) (coherentColimitUnitInteriorFirst B T)
    (coherentColimitUnitPointedTetrahedronChoice_vertex B T 0)
    (coherentColimitUnitFirstNativeRelation B T)

end SerrePositivity.InfinityCategories.F2
