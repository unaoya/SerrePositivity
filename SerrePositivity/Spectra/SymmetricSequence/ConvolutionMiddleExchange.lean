module

public import SerrePositivity.Spectra.SymmetricSequence.DayAssociativityComparisons
public import SerrePositivity.Spectra.SymmetricSequence.DayBraidingComparisons

/-! # 三重convolutionの先頭二因子を交換する標準射の公式 -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C]

/-- 二段の標準射の右結合表示。 -/
def tripleRightGenerator (A B D : SymmetricSequence C) (a b d : FiniteBijection) :
    A.obj a ⊗ (B.obj b ⊗ D.obj d) ⟶ (A ⊗ (B ⊗ D)).obj (a ⊗ (b ⊗ d)) :=
  A.obj a ◁ (convolutionUnit B D).app (b, d) ≫
    (convolutionUnit A (B ⊗ D)).app (a, b ⊗ d)

/-- 二段の標準射の左結合表示。 -/
def tripleLeftGenerator (A B D : SymmetricSequence C) (a b d : FiniteBijection) :
    (A.obj a ⊗ B.obj b) ⊗ D.obj d ⟶ ((A ⊗ B) ⊗ D).obj ((a ⊗ b) ⊗ d) :=
  (convolutionUnit A B).app (a, b) ▷ D.obj d ≫
    (convolutionUnit (A ⊗ B) D).app (a ⊗ b, d)

/-- convolutionの逆結合子を右結合の標準射上で計算する。 -/
@[reassoc]
lemma tripleRightGenerator_associator_inv (A B D : SymmetricSequence C)
    (a b d : FiniteBijection) :
    tripleRightGenerator A B D a b d ≫ (α_ A B D).inv.app (a ⊗ (b ⊗ d)) =
      (α_ (A.obj a) (B.obj b) (D.obj d)).inv ≫ tripleLeftGenerator A B D a b d ≫
        ((A ⊗ B) ⊗ D).map (α_ a b d).hom := by
  apply (cancel_mono ((α_ A B D).hom.app (a ⊗ (b ⊗ d)))).mp
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  erw [(α_ A B D).hom.naturality]
  unfold tripleLeftGenerator
  simp only [Category.assoc]
  erw [convolution_associator_generator_assoc]
  simp only [Iso.inv_hom_id_assoc]
  erw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.comp_id]
  rfl

/-- 添字の先頭二ブロックを交換し、右結合へ戻す射。 -/
def middleExchangeIndex (a b d : FiniteBijection) : b ⊗ (a ⊗ d) ⟶ a ⊗ (b ⊗ d) :=
  (α_ b a d).inv ≫ (β_ b a).hom ▷ d ≫ (α_ a b d).hom

/-- 先頭二因子を交換するconvolutionの射。 -/
def middleExchange (A B D : SymmetricSequence C) : A ⊗ (B ⊗ D) ⟶ B ⊗ (A ⊗ D) :=
  (α_ A B D).inv ≫ (β_ A B).hom ▷ D ≫ (α_ B A D).hom

/-- 三重convolutionの交換は、基礎圏の交換と添字のブロック交換で記述できる。 -/
@[reassoc]
lemma tripleRightGenerator_middleExchange (A B D : SymmetricSequence C)
    (a b d : FiniteBijection) :
    tripleRightGenerator A B D a b d ≫ (middleExchange A B D).app (a ⊗ (b ⊗ d)) =
      (α_ (A.obj a) (B.obj b) (D.obj d)).inv ≫
        (β_ (A.obj a) (B.obj b)).hom ▷ D.obj d ≫
          (α_ (B.obj b) (A.obj a) (D.obj d)).hom ≫
            tripleRightGenerator B A D b a d ≫ (B ⊗ (A ⊗ D)).map (middleExchangeIndex a b d) := by
  unfold middleExchange
  erw [NatTrans.comp_app, NatTrans.comp_app]
  rw [tripleRightGenerator_associator_inv_assoc]
  erw [((β_ A B).hom ▷ D ≫ (α_ B A D).hom).naturality]
  unfold tripleLeftGenerator
  simp only [Category.assoc]
  erw [NatTrans.comp_app]
  simp only [Category.assoc]
  erw [convolutionUnit_whiskerRight_assoc]
  rw [← comp_whiskerRight_assoc]
  erw [convolution_braiding_generator]
  simp only [comp_whiskerRight, Category.assoc]
  have h := (convolutionUnit (B ⊗ A) D).naturality
    (show (b ⊗ a, d) ⟶ (a ⊗ b, d) from ⟨(β_ b a).hom, 𝟙 d⟩)
  simp only [externalProductBifunctor_obj_map, CategoryTheory.Functor.map_id,
    whiskerLeft_id, Category.comp_id] at h
  change (((B ⊗ A).map (β_ b a).hom) ▷ D.obj d) ≫
    (convolutionUnit (B ⊗ A) D).app (a ⊗ b, d) =
    (convolutionUnit (B ⊗ A) D).app (b ⊗ a, d) ≫
      ((B ⊗ A) ⊗ D).map ((β_ b a).hom ▷ d) at h
  erw [reassoc_of% h]
  erw [(α_ B A D).hom.naturality_assoc, convolution_associator_generator_assoc]
  simp only [Category.assoc, tripleRightGenerator]
  erw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  rfl

end SerrePositivity.SymmetricSequence
