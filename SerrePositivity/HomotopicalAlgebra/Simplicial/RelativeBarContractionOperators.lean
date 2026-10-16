module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarIdentity

/-! # Compatibility of the identity-bar contraction interval with all simplicial operators -/

@[expose] public section
universe v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.BarConstruction
variable {D : Type uD} [Category.{vD} D] (F : D ⥤ SSet.{v})

abbrev identityLevelMap (d : D) {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :=
  ((commaLevels (𝟭 D) F).map θ).app d |>.toFunctor

abbrev contractionInterval (d : D) (n : SimplexCategoryᵒᵖ) :=
  SerrePositivity.NerveHomotopy.interval (identityContraction F d n)

lemma contractionInterval_operator_obj (d : D) {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m)
    (z : Fin 2 × CostructuredArrow (elementProjection (𝟭 D) F n) d) :
    (contractionInterval F d n ⋙ identityLevelMap F d θ).obj z =
      ((𝟭 (Fin 2)).prod (identityLevelMap F d θ) ⋙ contractionInterval F d m).obj z := by
  rcases z with ⟨q, e⟩
  fin_cases q
  · rfl
  · exact congrArg (identityPoint F d m)
      (congrArg (fun k => k e.left.val) ((F.map e.hom).naturality θ)).symm

private lemma comma_hom_heq {n : SimplexCategoryᵒᵖ} {d : D}
    {e e' s s' : CostructuredArrow (elementProjection (𝟭 D) F n) d}
    (he : e = s) (he' : e' = s') (f : e ⟶ e') (g : s ⟶ s')
    (h : f.left.hom ≍ g.left.hom) : f ≍ g := by
  cases he
  cases he'
  apply heq_of_eq
  apply CostructuredArrow.hom_ext
  apply Functor.Elements.hom_ext
  exact eq_of_heq h

/-- The full interval functors commute, including the mixed 0→1 part. -/
lemma contractionInterval_operator (d : D) {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    contractionInterval F d n ⋙ identityLevelMap F d θ =
      (𝟭 (Fin 2)).prod (identityLevelMap F d θ) ⋙ contractionInterval F d m := by
  apply CategoryTheory.Functor.hext (contractionInterval_operator_obj F d θ)
  intro x y f
  apply comma_hom_heq F
    (contractionInterval_operator_obj F d θ x) (contractionInterval_operator_obj F d θ y)
  rcases x with ⟨q, e⟩
  rcases y with ⟨r, e'⟩
  fin_cases q <;> fin_cases r
  · rfl
  · rfl
  · have h := leOfHom f.1
    change (1 : Fin 2) ≤ 0 at h
    exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) h)
  · rfl

end SerrePositivity.SimplicialModel.BarConstruction
