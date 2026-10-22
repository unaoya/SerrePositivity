module

public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
概要：元の係数射の逆三角形を、指定した三つの係数同型で移送する。
方針：共通係数同型の単射性で比較し、元の二つの可換式へ戻す。
規約：係数同型を選び直さない。使われ方：共通 kernel 上での元の π₂ 逆の比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.KST.LocalizingInvariants
variable {R : Type u} [CommRing R]

lemma moduleCoefficientInverse_triangle {A B C K L M T : ModuleCat R}
    (eA : K ≅ A) (eB : L ≅ B) (eC : M ≅ C)
    (f : A ⟶ C) (t : B ⟶ C) (a : K ⟶ M) (b : L ⟶ M)
    (ha : a ≫ eC.hom = eA.hom ≫ f) (hb : b ≫ eC.hom = eB.hom ≫ t)
    (r : T ⟶ A) (s : T ⟶ B) (hr : r ≫ f = s ≫ t) :
    (r ≫ eA.inv) ≫ a = (s ≫ eB.inv) ≫ b := by
  apply (cancel_mono eC.hom).1
  simp only [Category.assoc, ha, hb, Iso.inv_hom_id_assoc]
  exact hr

end SerrePositivity.KST.LocalizingInvariants
