module

public import SerrePositivity.CategoryTheory.AdjunctionHomLaws
public import SerrePositivity.CategoryTheory.Monoidal.HomEquivNaturality

/-! # 随伴を合成したHom同値への自然性の移送 -/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃ u₄ u₅

namespace SerrePositivity.AdjunctionCompositeNaturality

open CategoryTheory

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
  {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
  {M M' : D ⥤ E} {N N' : E ⥤ D} (b : M ⊣ N) (b' : M' ⊣ N')

/-- 第二の随伴の転置の自然性を、合成随伴の転置へ移した等式。 -/
def preLaw {X : C} {Y : E} (t : M'.obj (L.obj X) ⟶ M.obj (L.obj X))
    (g : M.obj (L.obj X) ⟶ Y) (p : N.obj Y ⟶ N'.obj Y) : Prop :=
  (a.comp b').homEquiv X Y (t ≫ g) = (a.comp b).homEquiv X Y g ≫ R.map p

/-- 前段の随伴の値域の自然性を使い、第二の転置の自然性を合成随伴へ送る。 -/
lemma pre {X : C} {Y : E} (t : M'.obj (L.obj X) ⟶ M.obj (L.obj X))
    (g : M.obj (L.obj X) ⟶ Y) (p : N.obj Y ⟶ N'.obj Y)
    (h : b'.homEquiv (L.obj X) Y (t ≫ g) = b.homEquiv (L.obj X) Y g ≫ p) :
    preLaw a b b' t g p := by
  unfold preLaw
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  change a.homEquiv X (N'.obj Y) (b'.homEquiv (L.obj X) Y (t ≫ g)) = _
  rw [h]
  exact a.homEquiv_naturality_right _ p

/-- 合成随伴の転置と別の同値を介して得た同値の自然性。 -/
def derivedPreLaw {X : C} {Y : E} {Z : Type u₄} {Z' : Type u₅}
    (r : (M.obj (L.obj X) ⟶ Y) ≃ Z) (r' : (M'.obj (L.obj X) ⟶ Y) ≃ Z')
    (p : N.obj Y ⟶ N'.obj Y) (h : Z → Z') (y : X ⟶ R.obj (N.obj Y)) : Prop :=
  HomEquivNaturality.derivedLaw ((a.comp b).homEquiv X Y) ((a.comp b').homEquiv X Y)
    r r' (fun k => k ≫ R.map p) h y

/-- 合成随伴の自然性と別の同値の自然性から、導いた同値の自然性を得る。 -/
lemma derived_pre {X : C} {Y : E} {Z : Type u₄} {Z' : Type u₅}
    (r : (M.obj (L.obj X) ⟶ Y) ≃ Z) (r' : (M'.obj (L.obj X) ⟶ Y) ≃ Z')
    (t : M'.obj (L.obj X) ⟶ M.obj (L.obj X)) (p : N.obj Y ⟶ N'.obj Y) (h : Z → Z')
    (hq : ∀ k, preLaw a b b' t k p) (hr : ∀ k, r' (t ≫ k) = h (r k))
    (y : X ⟶ R.obj (N.obj Y)) : derivedPreLaw a b b' r r' p h y :=
  HomEquivNaturality.derived ((a.comp b).homEquiv X Y) ((a.comp b').homEquiv X Y)
    r r' (fun k => t ≫ k) (fun k => k ≫ R.map p) h hq hr y

end SerrePositivity.AdjunctionCompositeNaturality
