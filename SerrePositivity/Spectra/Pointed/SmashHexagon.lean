module

public import SerrePositivity.Spectra.Pointed.SmashAssociator

/-!
# smash 積の hexagon

三変数の標準射に沿って交換と結合を比較する。
基点付き直積の射を射影で比較し、smash の二つの hexagon を証明する。
-/

@[expose] public section

universe v u

noncomputable section

namespace SerrePositivity.PointedObject

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- 基点付き直積の第一の hexagon。 -/
lemma prodAssoc_hexagon_forward (X Y Z : PointedObject C) :
    prodAssocHom X Y Z ≫ prodSwap X (prod Y Z) ≫ prodAssocHom Y Z X =
      prodMap (prodSwap X Y) (𝟙 Z) ≫ prodAssocHom Y X Z ≫ prodMap (𝟙 Y) (prodSwap X Z) := by
  apply prod_hom_ext
  · simp [prodAssocHom, prodSwap, prodMap, Category.assoc]
  · apply prod_hom_ext <;> simp [prodAssocHom, prodSwap, prodMap, Category.assoc]

/-- 基点付き直積の第二の hexagon。 -/
lemma prodAssoc_hexagon_reverse (X Y Z : PointedObject C) :
    prodAssocInv X Y Z ≫ prodSwap (prod X Y) Z ≫ prodAssocInv Z X Y =
      prodMap (𝟙 X) (prodSwap Y Z) ≫ prodAssocInv X Z Y ≫ prodMap (prodSwap X Z) (𝟙 Y) := by
  apply prod_hom_ext
  · apply prod_hom_ext <;> simp [prodAssocInv, prodSwap, prodMap, Category.assoc]
  · simp [prodAssocInv, prodSwap, prodMap, Category.assoc]

variable [MonoidalClosed C] [HasFiniteColimits C]

omit [MonoidalClosed C] in
@[reassoc] lemma leftTripleQuotient_innerSwap (X Y Z : PointedObject C) :
    leftTripleQuotient X Y Z ≫ smashMap (smashSwap X Y) (𝟙 Z) =
      prodMap (prodSwap X Y) (𝟙 Z) ≫ leftTripleQuotient Y X Z := by
  simp only [leftTripleQuotient, Category.assoc, smashQuotient_map]
  simp only [← Category.assoc, prodMap_comp, Category.comp_id, smashQuotient_swap]

omit [MonoidalClosed C] in
@[reassoc] lemma rightTripleQuotient_innerSwap (X Y Z : PointedObject C) :
    rightTripleQuotient X Y Z ≫ smashMap (𝟙 X) (smashSwap Y Z) =
      prodMap (𝟙 X) (prodSwap Y Z) ≫ rightTripleQuotient X Z Y := by
  simp only [rightTripleQuotient, Category.assoc, smashQuotient_map]
  simp only [← Category.assoc, prodMap_comp, Category.comp_id, smashQuotient_swap]

omit [MonoidalClosed C] in
@[reassoc] lemma rightTripleQuotient_outerSwap (X Y Z : PointedObject C) :
    rightTripleQuotient X Y Z ≫ smashSwap X (smash Y Z) =
      prodSwap X (prod Y Z) ≫ leftTripleQuotient Y Z X := by
  simp only [rightTripleQuotient, leftTripleQuotient, Category.assoc, smashQuotient_swap]
  rw [← Category.assoc, prodSwap_naturality, Category.assoc]

omit [MonoidalClosed C] in
@[reassoc] lemma leftTripleQuotient_outerSwap (X Y Z : PointedObject C) :
    leftTripleQuotient X Y Z ≫ smashSwap (smash X Y) Z =
      prodSwap (prod X Y) Z ≫ rightTripleQuotient Z X Y := by
  simp only [rightTripleQuotient, leftTripleQuotient, Category.assoc, smashQuotient_swap]
  rw [← Category.assoc, prodSwap_naturality, Category.assoc]

/-- smash 積の第一の hexagon。 -/
lemma smashAssoc_hexagon_forward (X Y Z : PointedObject C) :
    smashAssocHom X Y Z ≫ smashSwap X (smash Y Z) ≫ smashAssocHom Y Z X =
      smashMap (smashSwap X Y) (𝟙 Z) ≫ smashAssocHom Y X Z ≫
        smashMap (𝟙 Y) (smashSwap X Z) := by
  apply (cancel_epi (leftTripleQuotient X Y Z)).mp
  rw [leftTripleQuotient_assocHom_assoc, rightTripleQuotient_outerSwap_assoc,
    leftTripleQuotient_assocHom, leftTripleQuotient_innerSwap_assoc,
    leftTripleQuotient_assocHom_assoc, rightTripleQuotient_innerSwap]
  simpa only [Category.assoc] using
    congrArg (fun k ↦ k ≫ rightTripleQuotient Y Z X) (prodAssoc_hexagon_forward X Y Z)

/-- smash 積の第二の hexagon。 -/
lemma smashAssoc_hexagon_reverse (X Y Z : PointedObject C) :
    smashAssocInv X Y Z ≫ smashSwap (smash X Y) Z ≫ smashAssocInv Z X Y =
      smashMap (𝟙 X) (smashSwap Y Z) ≫ smashAssocInv X Z Y ≫
        smashMap (smashSwap X Z) (𝟙 Y) := by
  apply (cancel_epi (rightTripleQuotient X Y Z)).mp
  rw [rightTripleQuotient_assocInv_assoc, leftTripleQuotient_outerSwap_assoc,
    rightTripleQuotient_assocInv, rightTripleQuotient_innerSwap_assoc,
    rightTripleQuotient_assocInv_assoc, leftTripleQuotient_innerSwap]
  simpa only [Category.assoc] using
    congrArg (fun k ↦ k ≫ leftTripleQuotient Z X Y) (prodAssoc_hexagon_reverse X Y Z)

end SerrePositivity.PointedObject
