module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PresheafHomWeights
public import SerrePositivity.InfinityCategories.F1.RepresentableLimitCharacterization
public import SerrePositivity.InfinityCategories.Core.FunctorPointwiseLimitCriterion
public import SerrePositivity.InfinityCategories.Stable.SquareFunctorTransport

/-!
概要：Hom(F(−), d) の元の全前層値関手は、d の指定された全極限錐を保存する。
方針：元の全評価と全共変 Hom の自然比較を使い、同じ錐の各点極限性を示す。
規約：元の関手・錐・全係数を保持。添字と係数の底の quasicategory 性は不要。
使われ方：P_Σ 延長の全自然 Hom 表示の係数関手の連続性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の Hom 係数前層の全族は、同じ指定極限錐を全係数で各点極限へ送る。 -/
lemma presheafHomWeightDiagram_isPointwiseLimit {K C D : SSet.{u}} [Quasicategory D]
    (F : C ⟶ D) {p : K ⟶ D} (c : JoinCone p) (hc : IsLimitCone c) :
    IsPointwiseLimitCone (mapJoinCone (presheafHomWeightDiagram F)
      (JoinCone.ulift.{u, u + 1} c)) := by
  rintro ⟨x⟩
  let y : C _⦋0⦌ := SSet.opObjEquiv x
  change IsLimitCone (mapJoinCone
    (presheafHomWeightDiagram F ≫ presheafInfinityEvaluation y)
      (JoinCone.ulift.{u, u + 1} c))
  exact (covariantRepresentableInfinity_isLimit c hc (F.app _ y)).of_functorIso
    (FunctorIso.precomp (presheafHomWeightDiagram_evaluationIso F y).symm
      (JoinCone.ulift.{u, u + 1} c).val)

/-- 元の全 Hom 係数関手は、元の指定全極限錐を同じ前層圏の極限へ送る。 -/
lemma presheafHomWeightDiagram_map_isLimit {K C D : SSet.{u}} [Quasicategory D]
    (F : C ⟶ D) {p : K ⟶ D} (c : JoinCone p) (hc : IsLimitCone c) :
    IsLimitCone (mapJoinCone (presheafHomWeightDiagram F)
      (JoinCone.ulift.{u, u + 1} c)) :=
  isLimitCone_of_pointwise _ (presheafHomWeightDiagram_isPointwiseLimit F c hc)

end SerrePositivity.InfinityCategories.HomotopyLimits
