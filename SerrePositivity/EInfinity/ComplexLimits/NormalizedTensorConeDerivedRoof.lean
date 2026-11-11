module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorConeDerivedFamilyInverse
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorElementConstantRoof

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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
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
    Arrow.mk (normalizedTensorConeDerivedFamilyHom A X Y ≫
      normalizedTensorElementDerivedEvaluation A X Y) =
      Arrow.mk (normalizedTensorElementDerivedRoof A X Y) := by
  exact arrow_postcomp_eq _ _ (normalizedTensorConeDerivedFamilyHom_inverse_arrow A X Y)
    (normalizedTensorElementDerivedEvaluation A X Y)

lemma normalizedTensorElementDerivedRoofFamily_arrow :
    Arrow.mk (normalizedTensorElementDerivedRoofFamily A X Y) =
      Arrow.mk (normalizedTensorElementDerivedRoof A X Y) := by
  unfold normalizedTensorElementDerivedRoofFamily complexOrdinaryDerivedConstantIso
  exact arrow_transport_eq
    (congrArg (fun f => SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f))
      (complexOrdinaryDerivedConstant_eq A (normalizedTensorElementIndex A X Y) X))
    (congrArg (fun f => SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f))
      (complexOrdinaryDerivedConstant_eq A (normalizedTensorElementIndex A X Y) Y))
    (normalizedTensorElementDerivedRoof A X Y)

lemma normalizedTensorConeDerivedEvaluation_family_arrow :
    Arrow.mk (normalizedTensorConeDerivedFamilyHom A X Y ≫
      normalizedTensorElementDerivedEvaluation A X Y) =
      Arrow.mk (normalizedTensorElementDerivedRoofFamily A X Y) :=
  (normalizedTensorConeDerivedEvaluation_arrow A X Y).trans
    (normalizedTensorElementDerivedRoofFamily_arrow A X Y).symm

end SerrePositivity.EInfinity.ComplexLimits
