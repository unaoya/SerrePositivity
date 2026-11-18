module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeDerivedFamilyInverse
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorElementConstantRoof

/-!
概要：元の実 cone と評価の合成は、元の全導来屋根自身に両端表示込みで一致する。
方針：同じ augmentation の逆の全 Arrow 比較を右合成し、元の定値端点の等式輸送を保つ。
規約：大域 pinched 族との評価三角形は別に検証する。使われ方：元の大域屋根との全比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X Y : Complex A)

private lemma arrow_postcomp_eq {C : Type*} [Category* C] {x x' y z : C}
    (f : x ⟶ y) (g : x' ⟶ y) (h : Arrow.mk f = Arrow.mk g) (b : y ⟶ z) :
    Arrow.mk (f ≫ b) = Arrow.mk (g ≫ b) := by
  obtain ⟨hx, hy, hh⟩ := (Arrow.mk_eq_mk_iff f g).mp h
  simp only [eqToHom_refl, Category.comp_id] at hh
  apply (Arrow.mk_eq_mk_iff (f ≫ b) (g ≫ b)).mpr
  refine ⟨hx, rfl, ?_⟩
  simp only [eqToHom_refl, Category.comp_id]
  rw [hh, Category.assoc]

private lemma arrow_transport_eq {C : Type*} [Category* C] {x y x' y' : C}
    (hx : x = x') (hy : y = y') (f : x ⟶ y) :
    Arrow.mk (eqToHom hx.symm ≫ f ≫ eqToHom hy) = Arrow.mk f := by
  cases hx
  cases hy
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

lemma normalizedTensorConeDerivedEvaluation_arrow :
    Arrow.mk (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeDerivedFamilyHom A X Y ≫
      _root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedEvaluation A X Y) =
      Arrow.mk (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedRoof A X Y) := by
  exact _root_.SerrePositivity.ComplexLimits.arrow_postcomp_eq _ _ (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeDerivedFamilyHom_inverse_arrow A X Y)
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedEvaluation A X Y)

lemma normalizedTensorElementDerivedRoofFamily_arrow :
    Arrow.mk (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedRoofFamily A X Y) =
      Arrow.mk (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedRoof A X Y) := by
  unfold _root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedRoofFamily _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedConstantIso
  exact _root_.SerrePositivity.ComplexLimits.arrow_transport_eq
    (congrArg (fun f => SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f))
      (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedConstant_eq A (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) X))
    (congrArg (fun f => SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f))
      (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedConstant_eq A (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) Y))
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedRoof A X Y)

lemma normalizedTensorConeDerivedEvaluation_family_arrow :
    Arrow.mk (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeDerivedFamilyHom A X Y ≫
      _root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedEvaluation A X Y) =
      Arrow.mk (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedRoofFamily A X Y) :=
  (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeDerivedEvaluation_arrow A X Y).trans
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedRoofFamily_arrow A X Y).symm

end SerrePositivity.ComplexLimits
