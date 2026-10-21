module

public import SerrePositivity.InfinityCategories.HomotopyLimits.StandardCoconeKanLeg
public import SerrePositivity.InfinityCategories.HomotopyLimits.PresheafStandardUnitSquare

/-!
概要：実際の前層余極限の元の頂点脚を同じ比較で共役し、元の全評価 Kan 脚へ同定する。
方針：同じ全余錐の頂点評価辺を保持し、両 coslice 比較の頂点同型を使う。
規約：指定余錐・全脚・比較代表を保持し、底の quasicategory 性は要求しない。
使われ方：実際の前層余極限の非空有限積保存の全脚比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
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

/-- 元の全余錐脚の頂点評価は、実際の頂点関手による同じ脚の全一単体。 -/
lemma presheafCoconeImageLeg_apex :
    (coconeWholeEdgeApex q₀ q₁ (presheafCoconeImageLeg q c k).toTruncated).edge =
      (F2.nativeConeLeg (mapJoinCone (presheafCoconeVertexFunctor q)
        (JoinCone.ulift c)) k).edge :=
  congrArg (fun d => (F2.nativeConeLeg d k).edge) (presheafCoconeImageCone_apex q c)

/-- 元の実際の頂点脚を同じ比較で標準評価余極限頂点間へ共役した辺。 -/
def presheafColimitLegConjugate :=
  standardCoconeKanLegEdge (r ≫ evaluateFunctorAt x₀) (r ≫ evaluateFunctorAt x₁)
    (presheafEvaluationCoconeIso r q hq x₀) (presheafEvaluationCoconeIso r q hq x₁)
    (presheafCoconeImageLeg q c k).toTruncated

/-- 実際の同じ頂点脚の共役辺は、同じ元の評価脚の全空間 Kan 像と同じ Hom 類。 -/
lemma presheafColimitLegConjugate_homMk :
    homMk (totalKanNativeEdge (r ≫ evaluateFunctorAt x₀) (r ≫ evaluateFunctorAt x₁)
      (coherentTransformationTotalKanMap (r ≫ evaluateFunctorAt x₀) (r ≫ evaluateFunctorAt x₁)
        (intervalMappingVertexOfEdge (coconeWholeEdgeBottom q₀ q₁
          (presheafCoconeImageLeg q c k).toTruncated)))).toTruncated =
      homMk (presheafColimitLegConjugate q hq c k).toTruncated :=
  standardCoconeKanLeg_homMk (r ≫ evaluateFunctorAt x₀) (r ≫ evaluateFunctorAt x₁)
    (presheafEvaluationCoconeIso r q hq x₀) (presheafEvaluationCoconeIso r q hq x₁)
    (presheafCoconeImageLeg q c k).toTruncated

end SerrePositivity.InfinityCategories.HomotopyLimits
