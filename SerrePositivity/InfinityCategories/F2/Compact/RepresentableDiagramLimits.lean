module

public import SerrePositivity.InfinityCategories.F2.Compact.RepresentableRetractions
public import SerrePositivity.InfinityCategories.F1.Compact.HomCovariantComparison
public import SerrePositivity.InfinityCategories.F1.Yoneda.RepresentableLimitCharacterization
public import SerrePositivity.InfinityCategories.Core.FunctorPointwiseLimitExistence

/-!
概要：元の全共変表現可能関手の反変な図式は、反対圏の元の全極限錐を保存する。
方針：同じ図式の全評価を反対圏の元の共同 Hom へ同定し、各点の極限性で判定。
規約：値ごとの極限対象の存在で代用せず、指定された元の全錐像を保持する。
使われ方：compact 対象の有限余極限閉性のための全 Hom 極限表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact
variable {C K : SSet.{u}} [Quasicategory C]

/-- 元の全共変表現可能図式の評価は、反対圏の元の Yoneda の同じ評価。 -/
lemma covariantRepresentableDiagram_evaluation (y : C _⦋0⦌) :
    covariantRepresentableDiagram C ≫ evaluateFunctorAt (ULift.up y) =
      yonedaInfinityMap C.op ≫ presheafInfinityEvaluation (SSet.opObjEquiv.symm y) := by
  apply SSet.hom_ext
  intro n
  rfl

/-- 反対圏の元の全極限錐の共変表現可能像は、全係数で点ごとの極限錐。 -/
lemma covariantRepresentableDiagram_isPointwiseLimit {D : K ⟶ C.op}
    (c : JoinCone D) (hc : IsLimitCone c) :
    IsPointwiseLimitCone (mapJoinCone (covariantRepresentableDiagram C)
      (JoinCone.ulift.{u, u + 1} c)) := by
  intro y
  rcases y with ⟨y⟩
  change IsLimitCone (mapJoinCone
    (covariantRepresentableDiagram C ≫ evaluateFunctorAt (ULift.up y))
      (JoinCone.ulift.{u, u + 1} c))
  rw [covariantRepresentableDiagram_evaluation, ← homInfinityCovariant_eq_yonedaEvaluation]
  exact (covariantRepresentableInfinity_isLimit c hc (SSet.opObjEquiv.symm y)).of_functorIso
    (FunctorIso.precomp (homInfinityCovariant_covariantIso
      (C := C.op) (SSet.opObjEquiv.symm y)).symm (JoinCone.ulift.{u, u + 1} c).val)

/-- 元の全共変表現可能図式は、反対圏の同じ全極限錐を関手 ∞ 圏の極限へ写す。 -/
lemma covariantRepresentableDiagram_isLimit {D : K ⟶ C.op}
    (c : JoinCone D) (hc : IsLimitCone c) :
    IsLimitCone (mapJoinCone (covariantRepresentableDiagram C)
      (JoinCone.ulift.{u, u + 1} c)) :=
  isLimitCone_of_pointwise _ (covariantRepresentableDiagram_isPointwiseLimit c hc)

end SerrePositivity.InfinityCategories.F2.Compact
