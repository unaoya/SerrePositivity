module

public import SerrePositivity.KST.Spectra.InternalHomTensorAction
public import SerrePositivity.KST.Spectra.InternalHomTensor

/-!
概要：テンソル作用の Hom 写像は、構造射の随伴への後合成と一致する。
方針：二重 uncurry で評価射の自然性と結合子の相殺に帰着する。
規約：一般の閉モノイダル圏で証明する。使われ方：Ω 条件の写像空間への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.InternalHomExchange
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]

/-- テンソルした射を構造射と合成し curry すると、その随伴への後合成になる。 -/
lemma tensorHom_adjoint (S A B Z : C) (s : S ⊗ B ⟶ Z) :
    tensorHom S A B ≫ (ihom (S ⊗ A)).map s ≫ (InternalHomTensor.iso S A Z).hom =
      (ihom A).map (curry s) := by
  rw [InternalHomTensor.hom_eq]
  apply uncurry_injective
  apply uncurry_injective
  simp only [uncurry_natural_left, uncurry_curry, uncurry_ihom_map]
  rw [← Category.assoc, ← Category.assoc]
  rw [← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp]
  rw [associator_inv_naturality_right, MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc]
  rw [← uncurry_eq, uncurry_ihom_map, tensorHom_evaluation_assoc,
    Iso.inv_hom_id_assoc]

end SerrePositivity.KST.Spectra.InternalHomExchange
