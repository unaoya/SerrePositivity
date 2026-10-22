module

public import SerrePositivity.InfinityCategories.F2.Compact.DiscreteComponentLabels
public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation

/-!
概要：元の任意の弱ホモトピー同値は、連結成分上で全射。
方針：像に入らない成分を二つの離散ラベルで分離し、Kan 標的への前合成で検出する。
規約：元の始域の Kan 性を要求しない。実際の同じ射の π₀ 作用を扱う。
使われ方：元の全空間の Kan 置換単位から、余極限の指定点を回収する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact

/-- 元の始域の Kan 性を仮定せず、元の弱同値の同じ π₀ 作用の全射性を回収する。 -/
lemma weakHomotopyEquivalence_mapPiZero_surjective {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : IsWeakHomotopyEquivalence f) : Function.Surjective (SSet.mapπ₀ f) := by
  classical
  intro y
  by_contra hn
  let T := ULift.{u} Bool
  let a : SSet.π₀ Y → T := fun z ↦ if z = y then ULift.up true else ULift.up false
  let b : SSet.π₀ Y → T := fun _ ↦ ULift.up false
  let g := discreteComponentLabel Y a
  let h := discreteComponentLabel Y b
  have : KanComplex (nerve (Discrete T)) := discreteNerve_kanComplex T
  have he : f ≫ g = f ≫ h := by
    dsimp only [g, h]
    rw [discreteComponentLabel_pre, discreteComponentLabel_pre]
    apply congrArg (discreteComponentLabel X)
    funext z
    have hz : SSet.mapπ₀ f z ≠ y := fun hz ↦ hn ⟨z, hz⟩
    simp only [Function.comp_apply, a, b, ite_eq_right hz]
  have heπ : SSet.π₀.mk (functorVertex g) = SSet.π₀.mk (functorVertex h) := by
    apply (hf (nerve (Discrete T))).injective
    change SSet.π₀.mk (functorVertex (f ≫ g)) = SSet.π₀.mk (functorVertex (f ≫ h))
    rw [he]
  obtain ⟨v, hv⟩ := SSet.π₀.mk_surjective y
  have hh := congrArg (fun z ↦ discreteNerveComponent T
    (SSet.mapπ₀ (evaluateFunctorAt v) z)) heπ
  simp only [SSet.mapπ₀_mk, evaluateFunctorAt_functorVertex] at hh
  dsimp only [g, h] at hh
  rw [discreteComponentLabel_zero, discreteComponentLabel_zero, hv] at hh
  have hbad : (ULift.up true : T) = ULift.up false := by simpa only [a, b, ite_eq_left rfl] using hh
  exact Bool.noConfusion (congrArg ULift.down hbad)

end SerrePositivity.InfinityCategories.F2.Compact
