module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafInfinity
public import SerrePositivity.InfinityCategories.Core.FunctorPointwiseLimitExistence

/-!
概要：各点の極限から前層 ∞ 圏の極限を構成し、元の評価で保存・検出する。
方針：底の全頂点を反転・宇宙持ち上げした頂点と対応させ、一般の各点極限定理を使う。
規約：各点での存在を明示し、任意の大きい形状での存在は主張しない。
使われ方：F1-4、HTT 5.1.2.2–5.1.2.4。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {C : SSet.{u}} {J : SSet.{u + 1}} (p : J ⟶ PresheafInfinity C)

/-- 元の前層評価での極限の存在は、内部 Hom の全頂点での存在を与える。 -/
lemma presheafInfinity_hasPointwiseLimits
    (hp : ∀ x : C _⦋0⦌, HasLimit (p ≫ presheafInfinityEvaluation x)) :
    HasPointwiseLimits p := by
  intro k
  rcases k with ⟨k⟩
  obtain ⟨x, rfl⟩ := SSet.opObjEquiv.symm.surjective k
  exact hp x

/-- 各点で選んだ極限から、同じ前層図式の自然な極限全錐が存在する。 -/
lemma presheafInfinity_exists_limitCone_of_evaluation
    (hp : ∀ x : C _⦋0⦌, HasLimit (p ≫ presheafInfinityEvaluation x)) :
    ∃ c : JoinCone p, IsLimitCone c ∧ ∀ x : C _⦋0⦌,
      IsLimitCone (mapJoinCone (presheafInfinityEvaluation x) c) := by
  obtain ⟨c, hc⟩ := exists_pointwiseLimitCone p (presheafInfinity_hasPointwiseLimits p hp)
  exact ⟨c, isLimitCone_of_pointwise c hc,
    fun x ↦ hc (ULift.up (SSet.opObjEquiv.symm x))⟩

/-- 各点の極限の存在から前層図式の極限の存在を得る。 -/
lemma presheafInfinity_hasLimit_of_evaluation
    (hp : ∀ x : C _⦋0⦌, HasLimit (p ≫ presheafInfinityEvaluation x)) : HasLimit p :=
  hasLimit_of_hasPointwiseLimits p (presheafInfinity_hasPointwiseLimits p hp)

/-- 同じ前層錐が各点で極限なら、前層 ∞ 圏で極限。 -/
lemma presheafInfinity_isLimit_of_evaluation (c : JoinCone p)
    (hc : ∀ x : C _⦋0⦌, IsLimitCone (mapJoinCone (presheafInfinityEvaluation x) c)) :
    IsLimitCone c := by
  apply isLimitCone_of_pointwise c
  intro k
  rcases k with ⟨k⟩
  obtain ⟨x, rfl⟩ := SSet.opObjEquiv.symm.surjective k
  exact hc x

/-- 各点極限が存在すれば、任意の極限全錐を元の前層評価で保存する。 -/
lemma presheafInfinity_evaluation_isLimit
    (hp : ∀ x : C _⦋0⦌, HasLimit (p ≫ presheafInfinityEvaluation x))
    (c : JoinCone p) (hc : IsLimitCone c) (x : C _⦋0⦌) :
    IsLimitCone (mapJoinCone (presheafInfinityEvaluation x) c) :=
  isPointwiseLimitCone_of_isLimitCone_of_hasPointwiseLimits
    (presheafInfinity_hasPointwiseLimits p hp) c hc (ULift.up (SSet.opObjEquiv.symm x))

/-- 各点極限が存在する前層図式では、元の全評価が極限全錐を保存・検出する。 -/
lemma presheafInfinity_isLimit_iff_evaluation
    (hp : ∀ x : C _⦋0⦌, HasLimit (p ≫ presheafInfinityEvaluation x)) (c : JoinCone p) :
    IsLimitCone c ↔ ∀ x : C _⦋0⦌,
      IsLimitCone (mapJoinCone (presheafInfinityEvaluation x) c) :=
  ⟨presheafInfinity_evaluation_isLimit p hp c, presheafInfinity_isLimit_of_evaluation p c⟩

end SerrePositivity.InfinityCategories
