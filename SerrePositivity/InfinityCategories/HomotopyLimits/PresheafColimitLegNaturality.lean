module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PresheafApexRepresentative
public import SerrePositivity.InfinityCategories.HomotopyLimits.StandardCoconeLegNaturality
public import SerrePositivity.InfinityCategories.HomotopyLimits.PresheafColimitLegConjugate

/-!
概要：元の実際の前層余錐脚の可換式を、同じ頂点射影代表の類として保持する。
方針：元の頂点同型の順方向を、同じ coslice 代表の頂点辺へ置き換える。
規約：元の全余錐脚と両評価点を保持する。有限性は不要。
使われ方：標準有限全錐の端点表示に沿う自然性の輸送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
open SSet.Truncated.HomotopyCategory
variable {B C K : SSet.{u}}
  {r : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ PresheafInfinity C}
  (q : JoinCocone r)
  (hq : ∀ x : ((SSet.uliftFunctor.{u + 1, u}).obj C.op) _⦋0⦌,
    IsColimitCone (F1B.kanPostcomposeCocone (evaluateFunctorAt x) q))
  {p : K ⟶ C.op} (c : JoinCone p)
  (k : ((SSet.uliftFunctor.{u + 1, u}).obj K) _⦋0⦌)
local notation "x₀" => JoinCone.vertex (JoinCone.ulift c)
local notation "x₁" => NatTrans.app (CategoryTheory.Functor.map SSet.uliftFunctor p)
  (Opposite.op ⦋0⦌) k
local notation "q₀" => F1B.kanPostcomposeCocone (evaluateFunctorAt x₀) q
local notation "q₁" => F1B.kanPostcomposeCocone (evaluateFunctorAt x₁) q

/-- 同じ元の頂点射影代表の間で、実際の頂点脚と底変換の Kan 辺は可換。 -/
lemma presheafColimitLeg_representative_naturality :
    homMk (presheafEvaluationComparisonApexEdge r q hq
      (JoinCone.ulift c).vertex) ≫
      homMk (totalKanNativeEdge (r ≫ evaluateFunctorAt (JoinCone.ulift c).vertex)
        (r ≫ evaluateFunctorAt x₁) (coherentTransformationTotalKanMap
          (r ≫ evaluateFunctorAt (JoinCone.ulift c).vertex) (r ≫ evaluateFunctorAt x₁)
          (intervalMappingVertexOfEdge (coconeWholeEdgeBottom q₀ q₁
            (presheafCoconeImageLeg q c k).toTruncated)))).toTruncated =
    homMk (coconeWholeEdgeApex q₀ q₁ (presheafCoconeImageLeg q c k).toTruncated).toTruncated ≫
      homMk (presheafEvaluationComparisonApexEdge r q hq x₁) ≫
      eqToHom (congrArg HomotopyCategory.mk
        (F2.coherentDiagramTotalCocone_vertex (r ≫ evaluateFunctorAt x₁))) := by
  rw [presheafEvaluationComparisonApexEdge_homMk, presheafEvaluationComparisonApexEdge_homMk]
  exact standardCoconeKanLeg_naturality _ _ (presheafEvaluationCoconeIso r q hq _)
    (presheafEvaluationCoconeIso r q hq _) (presheafCoconeImageLeg q c k).toTruncated

end SerrePositivity.InfinityCategories.HomotopyLimits
