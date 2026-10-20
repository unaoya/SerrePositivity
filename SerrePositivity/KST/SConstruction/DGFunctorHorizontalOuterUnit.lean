module
public import SerrePositivity.KST.SConstruction.DGFunctorHorizontalComposition
public import SerrePositivity.KST.SConstruction.DGFunctorCoherence

/-! # 横合成の外側の恒等 dg 関手による単位則
概要：恒等 dg 関手の閉単位との横合成が、元の自然変換をそのまま回収する。
方針：等号移送と全対象評価を交換し、元の標的 dg 圏の単位則に戻す。
規約：閉単位と全パラメータを保持する。使われ方：dg 入力の単体的合成の単位。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded

private lemma leftUnitPair {A : Type u} [CommRing A] {C : Type*} [DGCategory A C]
    {P Q : Complex A} {X Y : C} (a : 𝟙_ (Complex A) ⟶ P)
    (f : P ⟶ (X ⟶[Complex A] X)) (b : Q ⟶ (X ⟶[Complex A] Y))
    (ha : a ≫ f = eId (Complex A) X) :
    (λ_ Q).inv ≫ (a ▷ Q) ≫ (f ⊗ₘ b) ≫ eComp (Complex A) X X Y = b := by
  change (λ_ Q).inv ≫ (a ⊗ₘ 𝟙 Q) ≫ (f ⊗ₘ b) ≫ eComp (Complex A) X X Y = b
  rw [tensorHom_comp_tensorHom_assoc, Category.id_comp, ha, tensorHom_def',
    Category.assoc, ← leftUnitor_inv_naturality_assoc, e_id_comp, Category.comp_id]

private lemma rightUnitPair {A : Type u} [CommRing A] {C : Type*} [DGCategory A C]
    {P Q : Complex A} {X Y : C} (a : 𝟙_ (Complex A) ⟶ P)
    (f : P ⟶ (Y ⟶[Complex A] Y)) (b : Q ⟶ (X ⟶[Complex A] Y))
    (ha : a ≫ f = eId (Complex A) Y) :
    (ρ_ Q).inv ≫ (Q ◁ a) ≫ (b ⊗ₘ f) ≫ eComp (Complex A) X Y Y = b := by
  change (ρ_ Q).inv ≫ (𝟙 Q ⊗ₘ a) ≫ (b ⊗ₘ f) ≫ eComp (Complex A) X Y Y = b
  rw [tensorHom_comp_tensorHom_assoc, Category.id_comp, ha, tensorHom_def,
    Category.assoc, ← rightUnitor_inv_naturality_assoc, e_comp_id, Category.comp_id]

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F₀ F₁ : DGFunctor A D E)

omit [Small.{u} E] in
/-- 恒等 dg 関手の閉単位を左から横合成すると、元の全パラメータを回収する。 -/
lemma dgFunctorHorizontal_left_unit :
    (λ_ (dgFunctorHom A D E F₀ F₁)).inv ≫
        dgFunctorIdentity A D D (DGFunctor.id D) ▷ dgFunctorHom A D E F₀ F₁ ≫
        dgFunctorHorizontal A D D E (DGFunctor.id D) (DGFunctor.id D) F₀ F₁ ≫
        dgFunctorHomTransport A D E (strictDGFunctor_id_comp F₀)
          (strictDGFunctor_id_comp F₁) = 𝟙 _ := by
  apply dgFunctorHom_ext
  intro x
  simp only [Category.assoc, dgFunctorHomTransport_π, eqToHom_refl, Category.comp_id,
    dgFunctorHorizontal_π]
  exact leftUnitPair _ _ _ ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ F₀.map x x)
      (dgFunctorIdentity_π A D D (DGFunctor.id D) x)).trans (F₀.map_id x)))

/-- 恒等 dg 関手の閉単位を右から横合成すると、元の全パラメータを回収する。 -/
lemma dgFunctorHorizontal_right_unit :
    (ρ_ (dgFunctorHom A D E F₀ F₁)).inv ≫
        dgFunctorHom A D E F₀ F₁ ◁ dgFunctorIdentity A E E (DGFunctor.id E) ≫
        dgFunctorHorizontal A D E E F₀ F₁ (DGFunctor.id E) (DGFunctor.id E) ≫
        dgFunctorHomTransport A D E (strictDGFunctor_comp_id F₀)
          (strictDGFunctor_comp_id F₁) = 𝟙 _ := by
  apply dgFunctorHom_ext
  intro x
  simp only [Category.assoc, dgFunctorHomTransport_π, eqToHom_refl, Category.comp_id,
    dgFunctorHorizontal_π, DGFunctor.id, EnrichedFunctor.id_map]
  exact rightUnitPair _ _ _ (dgFunctorIdentity_π A E E (DGFunctor.id E) (F₁.obj x))

end SerrePositivity.KST.SConstruction
