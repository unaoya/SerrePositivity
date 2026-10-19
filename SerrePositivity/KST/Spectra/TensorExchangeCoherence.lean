module

public import SerrePositivity.KST.Spectra.HomTensorStrength

/-!
概要：対称テンソルの三因子交換と結合子の整合性。
方針：braiding の六角形と対称性で因子を揃え、結合子の coherence を用いる。
規約：通常の閉構造は不要。使われ方：内部 Hom の strength の交換式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory
namespace SerrePositivity.KST.Spectra.HomTensorStrength
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

lemma exchange_tensor_left (S X A E : C) :
    (exchange (S ⊗ X) A E).hom ≫ A ◁ (α_ S X E).hom ≫
        (exchange A S (X ⊗ E)).hom =
      (α_ S X (A ⊗ E)).hom ≫ S ◁ (exchange X A E).hom := by
  simp only [exchange, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, tensorRight,
    Functor.flip, curriedTensor, BraidedCategory.braiding_tensor_left_hom,
    comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  have hm : (α_ A S X).hom ▷ E ≫ (α_ A (S ⊗ X) E).hom ≫
      A ◁ (α_ S X E).hom ≫ (α_ A S (X ⊗ E)).inv = (α_ (A ⊗ S) X E).hom := by
    monoidal
  have hmt := congrArg (fun f ↦ f ≫ (β_ A S).hom ▷ (X ⊗ E) ≫
    (α_ S A (X ⊗ E)).hom) hm
  simp only [Category.assoc] at hmt
  rw [hmt, associator_naturality_left_assoc,
    ← comp_whiskerRight_assoc (β_ S A).hom (β_ A S).hom (X ⊗ E),
    SymmetricCategory.symmetry, id_whiskerRight, Category.id_comp]
  monoidal

end SerrePositivity.KST.Spectra.HomTensorStrength
