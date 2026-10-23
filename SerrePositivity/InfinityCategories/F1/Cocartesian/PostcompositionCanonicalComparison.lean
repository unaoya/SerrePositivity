module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.QCatPostcompositionFiberComparison
public import SerrePositivity.InfinityCategories.F1.Cocartesian.PostcompositionDiagonalComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseLeftFibration

/-!
概要：実際の cocartesian 輸送の後合成 fiber の標準対角比較を、追加仮定なしで同値と証明する。
方針：元の後合成の Kan 性を使い、同じ宇宙の fiber 同型で標準比較を移す。
規約：元の比較との第二三角形の一致は別途証明する。
使われ方：元の固定成分比較の同値性を閉じるための標準 fiber 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable (F G : CocartesianTransportDiagramCategory (ULift.{u} (Fin 2)))
variable (b : ((SSet.uliftFunctor.{u + 1, u}).obj
  (SimplicialCategory.sHom (cocartesianTransportDiagramValue F (ULift.up 1))
    (cocartesianTransportDiagramValue G (ULift.up 1)))) _⦋0⦌)
local notation "A" => cocartesianTransportDiagramValue F (ULift.up 0)
local notation "B" => cocartesianTransportDiagramValue G (ULift.up 0)
local notation "Z" => cocartesianTransportDiagramValue G (ULift.up 1)
local notation "f₀₁" => CategoryTheory.Functor.map
  (cocartesianTransportDiagramValueFunctor G) strictIntervalIndexArrow
local notation "p₀" => quasicategoryCoreMap (CategoryTheory.Functor.map
  (ihom (F.val.obj (ULift.up 0))) (G.val.map strictIntervalIndexArrow))
local notation "b₀" => NatTrans.app (quasicategoryCoreMap
  (NatTrans.app (pre (F.val.map strictIntervalIndexArrow)) (G.val.obj (ULift.up 1))))
  (Opposite.op ⦋0⦌) b.down

local instance : LeftFibration (qCatPostcompositionMap A B Z f₀₁) := by
  letI := core_cocartesianIntervalPostHom_fibration G (F.val.obj (ULift.up 0))
  change LeftFibration ((SSet.uliftFunctor.{u + 1, u}).map p₀)
  infer_instance

/-- 元の後合成 fiber から同じ指定対角 fiber への、coherent 合成による標準比較。 -/
def cocartesianPostcompositionCanonicalComparison :
    (SSet.uliftFunctor.{u + 1, u}).obj (cocartesianIntervalPostcompositionFiber F G b) ⟶
      vertexFiber (compositionCorrespondenceDiagonal (X := CatInfinity.{u})
        (coherentNerveVertex A) (cocartesianIntervalCompositionFirstEdge G))
        (cocartesianPostcompositionDiagonalVertex F G b) :=
  (uliftVertexFiberIso.{u, u + 1} p₀ b₀).hom ≫
    qCatPostcompositionFiberComparison A B Z f₀₁ (ULift.up b₀)

attribute [local instance] compositionCorrespondenceDiagonal_fibration
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

local instance : KanComplex ((SSet.uliftFunctor.{u + 1, u}).obj
    (cocartesianIntervalPostcompositionFiber F G b)) := by
  letI := cocartesianIntervalPostcompositionFiber_kanComplex F G b
  infer_instance

/-- 実際の cocartesian 輸送の同じ標準対角 fiber 比較は、追加仮定なしに同値。 -/
lemma cocartesianPostcompositionCanonicalComparison_isQCatEquivalence :
    IsQCatEquivalence (cocartesianPostcompositionCanonicalComparison F G b) := by
  letI := core_cocartesianIntervalPostHom_fibration G (F.val.obj (ULift.up 0))
  letI : KanComplex (vertexFiber p₀ b₀) := vertexFiber_kanComplex_of_leftFibration _ _
  have hi : IsQCatEquivalence (uliftVertexFiberIso.{u, u + 1} p₀ b₀).hom :=
    (qCatEquivalenceOfIso (uliftVertexFiberIso.{u, u + 1} p₀ b₀)).isQCatEquivalence
  exact hi.comp (qCatPostcompositionFiberComparison_isQCatEquivalence A B Z f₀₁ (ULift.up b₀))

/-- 同じ標準 fiber 比較の包含は、元の包含の後の coherent 全体比較。 -/
lemma cocartesianPostcompositionCanonicalComparison_ι :
    cocartesianPostcompositionCanonicalComparison F G b ≫
        vertexFiberι (compositionCorrespondenceDiagonal (X := CatInfinity.{u})
          (coherentNerveVertex A) (cocartesianIntervalCompositionFirstEdge G))
          (cocartesianPostcompositionDiagonalVertex F G b) =
      (SSet.uliftFunctor.{u + 1, u}).map (vertexFiberι p₀ b₀) ≫
        coherentCompositionCorrespondence A B Z f₀₁ := by
  change ((uliftVertexFiberIso.{u, u + 1} p₀ b₀).hom ≫
    qCatPostcompositionFiberComparison A B Z f₀₁ (ULift.up b₀)) ≫
      vertexFiberι (compositionCorrespondenceDiagonal (coherentNerveVertex A)
        (coherentNerveEdge f₀₁))
        ((coherentHomIntervalComparison A Z).app (Opposite.op ⦋0⦌) (ULift.up b₀)) = _
  rw [Category.assoc, qCatPostcompositionFiberComparison_ι, ← Category.assoc]
  congr 1

end SerrePositivity.InfinityCategories
