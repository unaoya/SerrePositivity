module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.WeakIdentityQuotientPoint
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftFibrationCoslicePointFamily

/-! # 同じ商上の恒等点から、分数図式の実 unstraightening への coslice 比較を構成する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 元の同じ商像の coslice から、商上の同じ分数図式の小さい全空間への実写像。 -/
def weakQuotientCosliceUnit :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientDiagram h x) :=
  lift (𝟙 _) (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientFiberPoint h x)) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibrationCoslicePointFamily
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientDiagram h x))
      (q.hom.app (Opposite.op ⦋0⦌) x)

/-- この比較は元の Verdier 商の底を厳密に保つ。 -/
theorem weakQuotientCosliceUnit_projection : weakQuotientCosliceUnit h x ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientDiagram h x) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)) := by
  rw [weakQuotientCosliceUnit, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibrationCoslicePointFamily_projection,
    ← Category.assoc, lift_fst, Category.id_comp]

/-- 恒等錐での比較の値は、元の恒等 span から移した同じ実 fiber 点を厳密に回収する。 -/
theorem weakQuotientCosliceUnit_identity :
    (weakQuotientCosliceUnit h x).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone (q.hom.app (Opposite.op ⦋0⦌) x)) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientFiberPoint h x).val := by
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientDiagram h x)
  let b := q.hom.app (Opposite.op ⦋0⦌) x
  let v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) _⦋0⦌ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientFiberPoint h x
  have he : (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone b) : (Δ[0] : SSet.{u}) ⟶ _) ≫
      lift (𝟙 _) (SSet.const v) =
      (SSet.const v : (Δ[0] : SSet.{u}) ⟶ _) ≫
        lift (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone b)) (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b)) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, Category.comp_id, SSet.comp_const]
    · simp only [Category.assoc, lift_snd, Category.comp_id, SSet.comp_const]
  have hf : (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone b) : (Δ[0] : SSet.{u}) ⟶ _) ≫
      weakQuotientCosliceUnit h x = SSet.const v.val := by
    change (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone b) ≫ lift (𝟙 _) (SSet.const v)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibrationCoslicePointFamily p b = _
    rw [he, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibrationCoslicePointFamily_identity, SSet.const_comp]
    rfl
  have hh := congrArg SSet.yonedaEquiv hf
  simpa only [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_const] using hh

end SerrePositivity.KST.Fibration
