module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PresheafEvaluationUnitComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.NativeCoconeApexIso

/-!
概要：同じ元の評価 coslice 代表の頂点辺を、元の頂点同型の類と可逆性へ照合する。
方針：元の coslice 射影のホモトピー圏への関手性を使う。
規約：代表辺を変更せず、元の評価余錐と標準余錐の頂点を保持する。
使われ方：実際の有限錐像と標準全錐の比較辺の端点正規化。
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
variable {B C : SSet.{u}}
  (r : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ PresheafInfinity C)
  (q : JoinCocone r)
  (hq : ∀ x : ((SSet.uliftFunctor.{u + 1, u}).obj C.op) _⦋0⦌,
    IsColimitCone (F1B.kanPostcomposeCocone (evaluateFunctorAt x) q))
  (x : ((SSet.uliftFunctor.{u + 1, u}).obj C.op) _⦋0⦌)

/-- 元の同じ代表の頂点辺の類は、元の同じ coslice 比較の頂点同型の順方向。 -/
lemma presheafEvaluationComparisonApexEdge_homMk :
    homMk (presheafEvaluationComparisonApexEdge r q hq x) =
      (nativeCoconeApexIso (presheafEvaluationCoconeIso r q hq x)).hom := by
  change homMk ((nativeCoconeIsoRepresentative (presheafEvaluationCoconeIso r q hq x)).map
    ((truncation 2).map (sliceUnderProjection (r ≫ evaluateFunctorAt x)))) =
    (hoFunctor.map (sliceUnderProjection (r ≫ evaluateFunctorAt x))).toFunctor.map
      (presheafEvaluationCoconeIso r q hq x).hom
  rw [← nativeCoconeIsoRepresentative_homMk (presheafEvaluationCoconeIso r q hq x)]
  rfl

/-- 同じ元の評価 coslice 代表の頂点射影は可逆。 -/
lemma presheafEvaluationComparisonApexEdge_isInvertible :
    IsInvertibleEdge (X := SpaceInfinity.{u}) (presheafEvaluationComparisonApexEdge r q hq x) :=
  (nativeCoconeIsoRepresentative_isInvertible (presheafEvaluationCoconeIso r q hq x)).map
    (sliceUnderProjection (r ≫ evaluateFunctorAt x))

end SerrePositivity.InfinityCategories.HomotopyLimits
