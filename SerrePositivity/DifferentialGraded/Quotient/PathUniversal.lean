module
public import SerrePositivity.DifferentialGraded.Quotient.Paths

/-! # 内部微分を持つpath直和の普遍性と空部分圏の比較

最終dg商の収縮方程式を課す前の、直和の普遍性だけを記録する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 全path項に与えたchain map族を内部微分の直和から延長する。 -/
def desc (S : Set D) (x y : D) {T : Complex A} (f : ∀ w : Word S, term A D w x y ⟶ T) :
    internalHom A D S x y ⟶ T := Sigma.desc f

@[reassoc (attr := simp)]
lemma ι_desc (S : Set D) (x y : D) {T : Complex A}
    (f : ∀ w : Word S, term A D w x y ⟶ T) (w : Word S) :
    ι A D S x y w ≫ desc A D S x y f = f w := Sigma.ι_comp_desc f w

/-- 内部微分のpath直和からの射は、全path項のchain map族と同値。 -/
def homEquiv (S : Set D) (x y : D) (T : Complex A) :
    (internalHom A D S x y ⟶ T) ≃ (∀ w : Word S, term A D w x y ⟶ T) where
  toFun f w := ι A D S x y w ≫ f
  invFun := desc A D S x y
  left_inv f := by apply hom_ext A D S x y; intro w; simp
  right_inv f := by funext w; exact ι_desc A D S x y f w

/-- 空部分圏を通る中間対象はないので、有限語は必ず空。 -/
lemma word_empty {D : Type v} (w : Word (∅ : Set D)) : w = [] := by
  cases w with
  | nil => rfl
  | cons b w => exact False.elim b.property

/-- 空部分圏の場合、path直和は元のHom複体そのものである。 -/
def emptyHomIso (x y : D) : homObject A D x y ≅ internalHom A D ∅ x y where
  hom := originalHom A D ∅ x y
  inv := desc A D ∅ x y (fun w => eqToHom (by rw [word_empty w]; rfl))
  hom_inv_id := by simp [originalHom, ι, desc]
  inv_hom_id := by
    apply hom_ext A D ∅ x y
    intro w
    have hw := word_empty w
    subst w
    simp [originalHom, ι, desc]

end SerrePositivity.DifferentialGraded.DGQuotient
