module

public import SerrePositivity.InfinityCategories.F1.Yoneda.CanonicalYonedaUnstraighteningIdentity
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.SourceInitial
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.CoslicePinchedIso

/-!
概要：始点固定・終点固定の二つの恒等点を、元の twisted arrow の全空間で厳密に照合する。
方針：両方の元の恒等錐を定値の重みの射に戻し、反転と二重反転の定値射を計算する。
規約：全体の復元射から取った同じ評価点の像も保持する。
使われ方：c1 の fiber 輸送の始点を、始点固定の実際の恒等点輸送に揃える。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

local instance {C : SSet.{u}} [Quasicategory C] : Quasicategory (C.op ⊗ C) :=
  quasicategory_of_innerFibration (fst C.op C)

private lemma op_map_const {A X : SSet.{u}} (x : X _⦋0⦌) :
    SSet.opFunctor.map (SSet.const (X := A) x) =
      SSet.const (X := A.op) (SSet.opObjEquiv.symm x) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply SSet.opObjEquiv.injective
  change PinchedHom.constant x n =
    SSet.opObjEquiv (PinchedHom.constant (X := X.op) (SSet.opObjEquiv.symm x) n)
  rw [constant_opObjEquiv]

/-- 元の coslice の恒等錐は、Tw の定値の重みの射へ写る。 -/
lemma cosliceTwistedArrowMap_identity {C : SSet.{u}} (x : C _⦋0⦌) :
    (cosliceTwistedArrowMap (SSet.yonedaEquiv.symm x)).app (Opposite.op ⦋0⦌)
      (cosliceIdentityCone x) = SSet.const x := by
  change cosliceEdgewiseCollapse ⦋0⦌ ≫ SSet.const x = SSet.const x
  rw [SSet.comp_const]

/-- 両端交換と二重反転は、元の恒等点の定値の重みの射を厳密に戻す。 -/
lemma twistedArrowOppositeSwap_identity {C : SSet.{u}} (x : C _⦋0⦌) :
    (twistedArrowOppositeSwap C).app (Opposite.op ⦋0⦌)
      (SSet.const (SSet.opObjEquiv.symm x)) = SSet.const x := by
  change ((edgewiseWeightReverseIso ⦋0⦌).inv ≫
    SSet.opFunctor.map (SSet.const (SSet.opObjEquiv.symm x))) ≫
      (SSet.opFunctorCompOpFunctorIso.app C).hom = SSet.const x
  rw [op_map_const, SSet.comp_const, SSet.const_comp]
  rfl

/-- 反転 coslice から終点固定で取った恒等錐も、同じ元の Tw の恒等点へ写る。 -/
lemma cosliceOppositeTwistedArrowMap_identity {C : SSet.{u}} (x : C _⦋0⦌) :
    (cosliceOppositeTwistedArrowMap
      (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm x))).app (Opposite.op ⦋0⦌)
        (cosliceIdentityCone (SSet.opObjEquiv.symm x)) = SSet.const x := by
  change (twistedArrowOppositeSwap C).app (Opposite.op ⦋0⦌)
    ((cosliceTwistedArrowMap _).app _ (cosliceIdentityCone _)) = _
  rw [cosliceTwistedArrowMap_identity, twistedArrowOppositeSwap_identity]

/-- 始点固定の恒等点を全体へ含めると、同じ定値の重みの射を厳密に回収する。 -/
lemma twistedArrowSourceIdentity_fst {C : SSet.{u}} (x : C _⦋0⦌) :
    (pullback.fst (twistedArrowProjection C) (twistedArrowSourceInclusion x)).app
      (Opposite.op ⦋0⦌) (twistedArrowSourceIdentity x) = SSet.const x := by
  have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) (cosliceIdentityCone x))
    (cosliceToTwistedArrowSource_fst x)
  exact h.trans (cosliceTwistedArrowMap_identity x)

/-- 全体からの同じ評価点は、始点固定の元の恒等点を同じ復元射で送った点そのもの。 -/
lemma canonicalYonedaUnstraighteningIdentity_global_source
    {C : SSet.{u}} [Quasicategory C] (x : C _⦋0⦌) :
    (smallLeftUnstraighteningMap (representablePresheafInfinity x) (twistedArrowHomInfinity C)
      (twistedArrowTargetInclusion x)
      (representablePresheafInfinity_eq_targetRestriction x).symm).app
        (Opposite.op ⦋0⦌) (canonicalYonedaUnstraighteningIdentity x) =
    (leftStraighteningInfinityReconstruction (twistedArrowProjection C)).app (Opposite.op ⦋0⦌)
      ((pullback.fst (twistedArrowProjection C) (twistedArrowSourceInclusion x)).app
        (Opposite.op ⦋0⦌) (twistedArrowSourceIdentity x)) := by
  rw [canonicalYonedaUnstraighteningIdentity_global,
    cosliceOppositeTwistedArrowMap_identity, twistedArrowSourceIdentity_fst]

end SerrePositivity.InfinityCategories
