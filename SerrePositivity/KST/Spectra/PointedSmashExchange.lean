module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength
public import SerrePositivity.Spectra.PointedSimplicialSet.SmashUnderlyingCoherence

/-!
概要：基点を忘れる標準射と三因子交換の整合性。
方針：結合子・braiding の既存の商写像公式と、商写像の自然性を合成する。
規約：既存の productToSmash と exchange そのものの式。使われ方：Hom end の作用の忘却。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
namespace SerrePositivity.KST.Spectra.PointedSmashExchange
open PointedSimplicialSet

/-- 直積から smash への標準射と逆向き結合子の整合性。 -/
@[reassoc]
lemma associator_inv (A K Z : PointedSimplicialSet.{u}) :
    A.right ◁ productToSmash K Z ≫ productToSmash A (K ⊗ Z) ≫ (α_ A K Z).inv.right =
      (α_ A.right K.right Z.right).inv ≫ productToSmash A K ▷ Z.right ≫
        productToSmash (A ⊗ K) Z := by
  apply (cancel_mono (α_ A K Z).hom.right).mp
  rw [Category.assoc, Category.assoc, ← Under.comp_right, Iso.inv_hom_id,
    Under.id_right, Category.comp_id, Category.assoc, Category.assoc,
    productToSmash_associator, Iso.inv_hom_id_assoc]

/-- 直積から smash への標準射は、三因子の最初の二因子の交換と可換。 -/
@[reassoc]
lemma exchange (A K Z : PointedSimplicialSet.{u}) :
    A.right ◁ productToSmash K Z ≫ productToSmash A (K ⊗ Z) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange A K Z).hom.right =
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange A.right K.right Z.right).hom ≫
        K.right ◁ productToSmash A Z ≫ productToSmash K (A ⊗ Z) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    tensorRight, Functor.flip, curriedTensor, Under.comp_right, Category.assoc]
  rw [associator_inv_assoc]
  have hn := productToSmash_naturality (β_ A K).hom (𝟙 Z)
  simp only [Under.id_right, tensorHom_id] at hn
  rw [← reassoc_of% hn, ← Category.assoc (productToSmash A K ▷ Z.right),
    ← comp_whiskerRight, ← productToSmash_braiding, comp_whiskerRight]
  simp only [Category.assoc]
  rw [productToSmash_associator]

end SerrePositivity.KST.Spectra.PointedSmashExchange
