module

public import SerrePositivity.InfinityCategories.F1.CocartesianSecondTriangleFamily
public import SerrePositivity.InfinityCategories.F1.CocartesianPostcompositionCanonicalComparison

/-!
概要：元の対角 fiber 比較と標準比較の同じ三角形を、元の後合成 fiber 上で照合する。
方針：元の第二三角形の族の式を source fiber の同型で運び、標準全体比較の評価と比較する。
規約：同じ元の後合成 fiber と三角形への射を保持する。
使われ方：標準比較の同値性を元の固定成分比較へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable (F G : CocartesianTransportDiagramCategory (ULift.{u} (Fin 2)))
variable (b : ((SSet.uliftFunctor.{u + 1, u}).obj
  (SimplicialCategory.sHom (cocartesianTransportDiagramValue F (ULift.up 1))
    (cocartesianTransportDiagramValue G (ULift.up 1)))) _⦋0⦌)
local notation "A" => cocartesianTransportDiagramValue F (ULift.up 0)
local notation "B" => cocartesianTransportDiagramValue G (ULift.up 0)
local notation "Z" => cocartesianTransportDiagramValue G (ULift.up 1)
local notation "f₀₁" => (CategoryTheory.Functor.map G.val strictIntervalIndexArrow : B ⟶ Z)
local notation "g" => cocartesianIntervalCompositionFirstEdge G
local notation "d" => cocartesianPostcompositionDiagonalVertex F G b
local notation "p" => compositionCorrespondenceDiagonal (X := CatInfinity) (coherentNerveVertex A) g
local notation "p₀" => quasicategoryCoreMap (CategoryTheory.Functor.map
  (ihom (F.val.obj (ULift.up 0))) (G.val.map strictIntervalIndexArrow))
local notation "b₀" => NatTrans.app (quasicategoryCoreMap
  (NatTrans.app (pre (F.val.map strictIntervalIndexArrow)) (G.val.obj (ULift.up 1))))
  (Opposite.op ⦋0⦌) b.down
local notation "r" => Limits.pullback.fst
  (NatTrans.app (pre (SSet.Subcomplex.ι (horn 2 1))) CatInfinity)
  (composableHomHornMap (coherentNerveVertex A) g)

/-- 元の対角 fiber 比較の三角形は、元の包含からの同じ標準合成三角形の族。 -/
lemma cocartesianPostcompositionDiagonalComparison_triangle_uncurry :
    uncurry (cocartesianPostcompositionDiagonalComparison F G b ≫ vertexFiberι p d ≫ r) =
      (Δ[2] ◁ (SSet.uliftFunctor.{u + 1, u}).map (vertexFiberι p₀ b₀)) ≫
        coherentCompositionFixedTriangle A B Z f₀₁ := by
  rw [cocartesianPostcompositionDiagonalComparison_triangle, uncurry_natural_left,
    cocartesianIntervalSecondTriangleMap_uncurry,
    cocartesianHomFixedComponentComparison_secondTriangle,
    ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
    cocartesianHomSourcePostcompositionFiberIso_inv_component_zero]

/-- 標準対角 fiber 比較の三角形も、元の包含からの同じ標準合成三角形の族。 -/
lemma cocartesianPostcompositionCanonicalComparison_triangle_uncurry :
    uncurry (cocartesianPostcompositionCanonicalComparison F G b ≫ vertexFiberι p d ≫ r) =
      (Δ[2] ◁ (SSet.uliftFunctor.{u + 1, u}).map (vertexFiberι p₀ b₀)) ≫
        coherentCompositionFixedTriangle A B Z f₀₁ := by
  have ht : coherentCompositionCorrespondence A B Z f₀₁ ≫ r =
      curry (coherentCompositionFixedTriangle A B Z f₀₁) :=
    coherentCompositionCorrespondence_triangle A B Z f₀₁
  rw [← Category.assoc, cocartesianPostcompositionCanonicalComparison_ι, Category.assoc]
  dsimp only [cocartesianTransportDiagramValueFunctor]
  rw [ht, uncurry_natural_left, uncurry_curry]

end SerrePositivity.InfinityCategories
