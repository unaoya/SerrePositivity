module
public import SerrePositivity.KST.SConstruction.DGFunctorHorizontalComposition
public import SerrePositivity.DifferentialGraded.Category.Tensor

/-! # 元の横合成による tensor dg 単位の保存
概要：全次数の横合成が元の二つの閉単位から、合成関手の同じ閉単位を回収する。
方針：前後合成の単位保存を使い、標的の豊穣左単位律へ戻す。
規約：元の tensor 単位の比較写像を保持する。使われ方：横合成の dg 関手化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded
private lemma tensorUnitCompose {A : Type u} [CommRing A] {U V X Y Z : Complex A}
    (a : 𝟙_ (Complex A) ⟶ U) (b : 𝟙_ (Complex A) ⟶ V) (r : U ⟶ X) (s : V ⟶ Y)
    (c : X ⊗ Y ⟶ Z) :
    (λ_ (𝟙_ (Complex A))).inv ≫ (a ⊗ₘ b) ≫ ((r ⊗ₘ s) ≫ c) =
      (λ_ (𝟙_ (Complex A))).inv ≫ ((a ≫ r) ⊗ₘ (b ≫ s)) ≫ c := by
  simp only [tensorHom_comp_tensorHom_assoc]

/-- 二つの同じ閉単位の tensor 合成は、元の豊穣単位を回収する。 -/
lemma dgEnrichedUnitsMultiply {A : Type u} [CommRing A]
    {C : Type*} [DGCategory A C] (X : C) :
    (λ_ (𝟙_ (Complex A))).inv ≫ (eId (Complex A) X ⊗ₘ eId (Complex A) X) ≫
      eComp (Complex A) X X X = eId (Complex A) X := by
  rw [tensorHom_def', Category.assoc, ← leftUnitor_inv_naturality_assoc,
    e_id_comp, Category.comp_id]

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (B : Type t) [DGCategory A B]

/-- 元の二つの閉単位の横合成は、元の合成関手の同じ閉単位。 -/
lemma dgFunctorHorizontal_identity (F : DGFunctor A D E) (G : DGFunctor A E B) :
    (λ_ (𝟙_ (Complex A))).inv ≫
      (dgFunctorIdentity A D E F ⊗ₘ dgFunctorIdentity A E B G) ≫
        dgFunctorHorizontal A D E B F F G G = dgFunctorIdentity A D B (F.comp G) := by
  change (λ_ (𝟙_ (Complex A))).inv ≫
      (dgFunctorIdentity A D E F ⊗ₘ dgFunctorIdentity A E B G) ≫
      ((dgFunctorHomPost A D E B G F F ⊗ₘ dgFunctorHomPre A E B D F G G) ≫
        dgFunctorComposition A D B (F.comp G) (F.comp G) (F.comp G)) = _
  refine (tensorUnitCompose _ _ _ _ _).trans ?_
  rw [dgFunctorHomPost_identity A D E B G F, dgFunctorHomPre_identity A E B D F G]
  exact dgEnrichedUnitsMultiply (F.comp G)

local instance horizontalSourceTensorEnrichment :
    DGCategory A (DGTensorCategory A (DGFunctor A D E) (DGFunctor A E B)) :=
  dgTensorEnrichment A (DGFunctor A D E) (DGFunctor A E B)

/-- 横合成は、元の tensor dg 圏の閉単位を厳密に保つ。 -/
lemma dgFunctorHorizontal_tensor_identity (F : DGFunctor A D E) (G : DGFunctor A E B) :
    eId (C := DGTensorCategory A (DGFunctor A D E) (DGFunctor A E B))
        (Complex A) (F, G) ≫
      dgFunctorHorizontal A D E B F F G G = dgFunctorIdentity A D B (F.comp G) := by
  rw [dgTensor_identity]
  exact dgFunctorHorizontal_identity A D E B F G

end SerrePositivity.KST.SConstruction
