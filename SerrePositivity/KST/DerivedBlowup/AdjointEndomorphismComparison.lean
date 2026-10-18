module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
概要：KST §3.1 の重み付き比較を指定随伴で移す一般補題。
方針：共役対応の単位公式と mate の自然性で Hom 同値の像を計算する。
規約：任意の自然自己射で成立し、同型性は後で適用する。
使われ方：canonical な捻り比較の可換式と可逆性。
-/

@[expose] public noncomputable section

universe u v w z

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D]

/-- 概要：左随伴の自然自己射による前合成は Hom 同値で右 mate による後合成となる。
方針：単位公式で右 mate を左自己射へ戻し、mate の自然性を使う。
規約：KST §3.1。使われ方：指定導来係数拡大比較の随伴像を計算する。 -/
theorem adjointEndomorphism_homEquiv {L : C ⥤ D} {R : D ⥤ C}
    (A : L ⊣ R) (α : L ⟶ L) {X : C} {Y : D} (f : L.obj X ⟶ Y) :
    A.homEquiv X Y (α.app X ≫ f) =
      A.homEquiv X Y f ≫ (conjugateEquiv A A α).app Y := by
  let β := conjugateEquiv A A α
  have hu := unit_conjugateEquiv A A α X
  calc
    A.homEquiv X Y (α.app X ≫ f) =
        (A.unit.app X ≫ R.map (α.app X)) ≫ R.map f := by
      rw [A.homEquiv_unit, CategoryTheory.Functor.map_comp, Category.assoc]
    _ = (A.unit.app X ≫ β.app (L.obj X)) ≫ R.map f := by rw [hu]
    _ = (A.unit.app X ≫ R.map f) ≫ β.app Y := by
      rw [Category.assoc, ← β.naturality f, Category.assoc]
    _ = _ := by rw [A.homEquiv_unit]

end SerrePositivity.KST.DerivedBlowup
