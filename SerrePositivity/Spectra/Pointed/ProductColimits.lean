module

public import SerrePositivity.Spectra.Pointed.SmashUnit
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# 基点付き直積と連結余極限

基点付き直積は、基点付き対象の余積を一般には保存しない。
一方、基礎圏の閉構造と under 圏の忘却の性質から、pushout は保存する。
余積から出る基礎圏の射の判定と、直積によるエピ射の保存も証明する。
smash の商を一つずつ取って三変数の普遍性へ進むための一般的な基盤。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.PointedObject

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- 基点付き対象の右からの直積関手。 -/
def prodRightFunctor (Z : PointedObject C) : PointedObject C ⥤ PointedObject C where
  obj X := prod X Z
  map f := prodMap f (𝟙 Z)
  map_id X := prodMap_id X Z
  map_comp f g := by simp

/-- 直積を取ってから基点を忘れることは、基点を忘れて直積を取ることと自然同型。 -/
def prodRightForgetIso (Z : PointedObject C) :
    prodRightFunctor Z ⋙ forget ≅ forget ⋙ tensorRight Z.right :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro X Y f
    simp [prodRightFunctor, forget, prodMap_right])

/-- 基点付き対象の左からの直積関手。 -/
def prodLeftFunctor (X : PointedObject C) : PointedObject C ⥤ PointedObject C where
  obj Y := prod X Y
  map f := prodMap (𝟙 X) f
  map_id Y := prodMap_id X Y
  map_comp f g := by simp

/-- 左直積と忘却も、基礎圏の左直積と自然同型に両立する。 -/
def prodLeftForgetIso (X : PointedObject C) :
    prodLeftFunctor X ⋙ forget ≅ forget ⋙ tensorLeft X.right :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro Y Z f
    simp [prodLeftFunctor, forget, prodMap_right])

variable [HasFiniteColimits C]

/-- 基点付き余積から出る基礎圏の射は、二つの成分上で決まる。
一致する基点を行き先に付け、under 圏の余積の普遍性へ戻す。 -/
lemma coprod_right_hom_ext {X Y : PointedObject C} {T : C}
    (f g : (X ⨿ Y).right ⟶ T)
    (h₁ : (coprod.inl : X ⟶ X ⨿ Y).right ≫ f = (coprod.inl : X ⟶ X ⨿ Y).right ≫ g)
    (h₂ : (coprod.inr : Y ⟶ X ⨿ Y).right ≫ f = (coprod.inr : Y ⟶ X ⨿ Y).right ≫ g) : f = g := by
  have hp : (X ⨿ Y).hom ≫ f = (X ⨿ Y).hom ≫ g := by
    rw [← Under.w (coprod.inl : X ⟶ X ⨿ Y), Category.assoc, h₁]
    simp
  let F : X ⨿ Y ⟶ Under.mk ((X ⨿ Y).hom ≫ f) := Under.homMk f rfl
  let G : X ⨿ Y ⟶ Under.mk ((X ⨿ Y).hom ≫ f) := Under.homMk g hp.symm
  have h : F = G := coprod.hom_ext
    (Under.UnderMorphism.ext h₁) (Under.UnderMorphism.ext h₂)
  exact congrArg Under.Hom.right h

variable [MonoidalClosed C]

attribute [local instance] BraidedCategory.ofCartesianMonoidalCategory

/-- 基点付き余積との基礎圏の直積から出る射は、二つの成分上で決まる。
基礎圏の直積の右随伴へ移し、余積の等式判定を使う。 -/
lemma coprod_right_tensor_hom_ext {X Y : PointedObject C} {Z T : C}
    (f g : (X ⨿ Y).right ⊗ Z ⟶ T)
    (h₁ : ((coprod.inl : X ⟶ X ⨿ Y).right ▷ Z) ≫ f = ((coprod.inl : X ⟶ X ⨿ Y).right ▷ Z) ≫ g)
    (h₂ : ((coprod.inr : Y ⟶ X ⨿ Y).right ▷ Z) ≫ f =
      ((coprod.inr : Y ⟶ X ⨿ Y).right ▷ Z) ≫ g) : f = g := by
  let adj := Adjunction.ofIsLeftAdjoint (tensorRight Z)
  apply (adj.homEquiv _ _).injective
  apply coprod_right_hom_ext
  · have h := congrArg (adj.homEquiv _ _) h₁
    change adj.homEquiv _ _ ((tensorRight Z).map (coprod.inl : X ⟶ X ⨿ Y).right ≫ f) =
      adj.homEquiv _ _ ((tensorRight Z).map (coprod.inl : X ⟶ X ⨿ Y).right ≫ g) at h
    rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_left] at h
    exact h
  · have h := congrArg (adj.homEquiv _ _) h₂
    change adj.homEquiv _ _ ((tensorRight Z).map (coprod.inr : Y ⟶ X ⨿ Y).right ≫ f) =
      adj.homEquiv _ _ ((tensorRight Z).map (coprod.inr : Y ⟶ X ⨿ Y).right ≫ g) at h
    rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_left] at h
    exact h

/-- 余積との基点付き右直積から出る射の二成分による等式判定。 -/
lemma prodRightCoprod_hom_ext {X Y Z T : PointedObject C}
    (f g : prod (X ⨿ Y) Z ⟶ T)
    (h₁ : prodMap (coprod.inl : X ⟶ X ⨿ Y) (𝟙 Z) ≫ f =
      prodMap coprod.inl (𝟙 Z) ≫ g)
    (h₂ : prodMap (coprod.inr : Y ⟶ X ⨿ Y) (𝟙 Z) ≫ f =
      prodMap coprod.inr (𝟙 Z) ≫ g) : f = g := by
  apply Under.UnderMorphism.ext
  apply coprod_right_tensor_hom_ext
  · simpa only [Under.comp_right, prodMap_right, Under.id_right, tensorHom_id] using
      congrArg Under.Hom.right h₁
  · simpa only [Under.comp_right, prodMap_right, Under.id_right, tensorHom_id] using
      congrArg Under.Hom.right h₂

/-- 余積との左直積から出る射も、二つの成分で判定できる。 -/
lemma prodLeftCoprod_hom_ext {X Y Z T : PointedObject C}
    (f g : prod X (Y ⨿ Z) ⟶ T)
    (h₁ : prodMap (𝟙 X) (coprod.inl : Y ⟶ Y ⨿ Z) ≫ f =
      prodMap (𝟙 X) coprod.inl ≫ g)
    (h₂ : prodMap (𝟙 X) (coprod.inr : Z ⟶ Y ⨿ Z) ≫ f =
      prodMap (𝟙 X) coprod.inr ≫ g) : f = g := by
  apply (cancel_epi (prodSwap (Y ⨿ Z) X)).mp
  apply prodRightCoprod_hom_ext
  · rw [prodSwap_naturality_assoc, h₁, prodSwap_naturality_assoc]
  · rw [prodSwap_naturality_assoc, h₂, prodSwap_naturality_assoc]

omit [HasFiniteColimits C] in
/-- 基点付き直積はエピ射を保つ。
under 圏でのエピ性を基礎圏へ移し、閉構造による直積の左随伴性を使う。 -/
instance prodMap_epi {X Y X' Y' : PointedObject C} (f : X ⟶ X') (g : Y ⟶ Y')
    [Epi f] [Epi g] : Epi (prodMap f g) := by
  have : Epi (prodMap f g).right := by
    rw [prodMap_right, tensorHom_def]
    change Epi ((tensorRight Y.right).map f.right ≫ (tensorLeft X'.right).map g.right)
    infer_instance
  exact Under.epi_of_epi_right (prodMap f g)

/-- 基点付き直積は pushout を保存する。
忘却が連結余極限を作ることと、基礎圏の直積の余極限保存から従う。 -/
instance prodRight_preservesPushouts (Z : PointedObject C) :
    PreservesColimitsOfShape WalkingSpan (prodRightFunctor Z) := by
  let : PreservesColimitsOfShape WalkingSpan (forget ⋙ tensorRight Z.right) := inferInstance
  let : PreservesColimitsOfShape WalkingSpan (prodRightFunctor Z ⋙ forget) :=
    preservesColimitsOfShape_of_natIso (prodRightForgetIso Z).symm
  exact preservesColimitsOfShape_of_reflects_of_preserves (prodRightFunctor Z) forget

/-- 基点付き左直積も pushout を保存する。 -/
instance prodLeft_preservesPushouts (X : PointedObject C) :
    PreservesColimitsOfShape WalkingSpan (prodLeftFunctor X) := by
  let : PreservesColimitsOfShape WalkingSpan (forget ⋙ tensorLeft X.right) := inferInstance
  let : PreservesColimitsOfShape WalkingSpan (prodLeftFunctor X ⋙ forget) :=
    preservesColimitsOfShape_of_natIso (prodLeftForgetIso X).symm
  exact preservesColimitsOfShape_of_reflects_of_preserves (prodLeftFunctor X) forget

end SerrePositivity.PointedObject
