module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.LocalizedHomDiagram
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryResolutionPairs

/-! # Ordinary localized morphisms label every raw mixed resolution simplex

The two actual resolution augmentations are inverted in the ordinary
localization. This is invariant under all simplicial operators and natural
under all actual resolution maps, without a simplicial value model.
-/

@[expose] public section
universe v u vH uH
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomotopicalAlgebra Opposite

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryMappingClassLabel

lemma fraction_naturality {H : Type uH} [Category.{vH} H]
    {A A' B B' X X' Y Y' : H} (a : A ≅ X) (a' : A' ≅ X')
    (b : Y ≅ B) (b' : Y' ≅ B') (l : A' ⟶ A) (r : B ⟶ B')
    (f : X' ⟶ X) (g : Y ⟶ Y') (h : A ⟶ B)
    (hs : l ≫ a.hom = a'.hom ≫ f) (ht : b.hom ≫ r = g ≫ b'.hom) :
    a'.inv ≫ l ≫ h ≫ r ≫ b'.inv = f ≫ a.inv ≫ h ≫ b.inv ≫ g := by
  have hl : a'.inv ≫ l = f ≫ a.inv := by
    simpa [Category.assoc] using congrArg (fun k => a'.inv ≫ k ≫ a.inv) hs
  have hr : r ≫ b'.inv = b.inv ≫ g := by
    simpa [Category.assoc] using congrArg (fun k => b.inv ≫ k ≫ b'.inv) ht
  calc
    _ = (a'.inv ≫ l) ≫ h ≫ (r ≫ b'.inv) := by simp only [Category.assoc]
    _ = (f ≫ a.inv) ≫ h ≫ (b.inv ≫ g) := by rw [hl, hr]
    _ = _ := by simp only [Category.assoc]

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {H : Type uH} [Category.{vH} H] (Q : C ⥤ H)
  [Q.IsLocalization (weakEquivalences C)]
  (R : OrdinaryResolutionPairs.Index (C := C))

abbrev source (n : SimplexCategory) := R.1.unop.resolution.augmentation.app n
abbrev target (n : SimplexCategory) := (R.2.unop.resolution.augmentation.app n).unop

def sourceIso (n : SimplexCategory) :
    Q.obj (R.1.unop.resolution.obj.obj n) ≅ Q.obj R.1.unop.base :=
  Localization.isoOfHom Q (weakEquivalences C) (source R n)
    (R.1.unop.resolution.augmentation_weakEquivalence n)

lemma target_weakEquivalence (n : SimplexCategory) : weakEquivalences C (target R n) := by
  have : WeakEquivalence (R.2.unop.resolution.augmentation.app n) :=
    ⟨R.2.unop.resolution.augmentation_weakEquivalence n⟩
  exact mem_weakEquivalences (target R n)

def targetIso (n : SimplexCategory) :
    Q.obj R.2.unop.base.unop ≅ Q.obj (R.2.unop.resolution.obj.obj n).unop :=
  Localization.isoOfHom Q (weakEquivalences C) (target R n)
    (target_weakEquivalence R n)

def label (n : SimplexCategoryᵒᵖ) (f : (OrdinaryResolutionPairs.raw.obj R).obj n) :
    LocalizedHomDiagram.value Q (OrdinaryResolutionPairs.projection.obj R) :=
  (LocalizedHomDiagram.equiv Q _).symm
    ((sourceIso Q R n.unop).inv ≫ Q.map f ≫ (targetIso Q R n.unop).inv)

lemma label_equiv (n : SimplexCategoryᵒᵖ) (f : (OrdinaryResolutionPairs.raw.obj R).obj n) :
    LocalizedHomDiagram.equiv Q _ (label Q R n f) =
      (sourceIso Q R n.unop).inv ≫ Q.map f ≫ (targetIso Q R n.unop).inv :=
  (LocalizedHomDiagram.equiv Q _).apply_symm_apply _

lemma label_operator {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m)
    (f : (OrdinaryResolutionPairs.raw.obj R).obj n) :
    label Q R m ((OrdinaryResolutionPairs.raw.obj R).map θ f) = label Q R n f := by
  apply (LocalizedHomDiagram.equiv Q _).injective
  rw [label_equiv, label_equiv]
  change (sourceIso Q R m.unop).inv ≫
      Q.map (R.1.unop.resolution.obj.map θ.unop ≫ f ≫
        (R.2.unop.resolution.obj.map θ.unop).unop) ≫ (targetIso Q R m.unop).inv = _
  rw [Q.map_comp, Q.map_comp]
  have hs := R.1.unop.resolution.augmentation.naturality θ.unop
  have ht := congrArg Quiver.Hom.unop
    (R.2.unop.resolution.augmentation.naturality θ.unop)
  change R.1.unop.resolution.obj.map θ.unop ≫ source R n.unop =
    source R m.unop ≫ 𝟙 _ at hs
  change target R n.unop ≫ (R.2.unop.resolution.obj.map θ.unop).unop =
    𝟙 _ ≫ target R m.unop at ht
  have h := fraction_naturality (sourceIso Q R n.unop) (sourceIso Q R m.unop)
    (targetIso Q R n.unop) (targetIso Q R m.unop)
    (Q.map (R.1.unop.resolution.obj.map θ.unop))
    (Q.map (R.2.unop.resolution.obj.map θ.unop).unop) (𝟙 _) (𝟙 _) (Q.map f)
    (by
      change Q.map _ ≫ Q.map _ = Q.map _ ≫ 𝟙 _
      simpa only [Q.map_comp, Q.map_id,
        Category.comp_id] using congrArg Q.map hs)
    (by
      change Q.map _ ≫ Q.map _ = 𝟙 _ ≫ Q.map _
      simpa only [Q.map_comp, Q.map_id, Category.id_comp] using congrArg Q.map ht)
  simpa only [Category.assoc, Category.id_comp, Category.comp_id] using h

lemma label_base {R S : OrdinaryResolutionPairs.Index (C := C)} (k : R ⟶ S)
    (n : SimplexCategoryᵒᵖ) (f : (OrdinaryResolutionPairs.raw.obj R).obj n) :
    label Q S n ((OrdinaryResolutionPairs.raw.map k).app n f) =
      (LocalizedHomDiagram.types Q).map (OrdinaryResolutionPairs.projection.map k)
        (label Q R n f) := by
  apply (LocalizedHomDiagram.equiv Q _).injective
  rw [label_equiv, LocalizedHomDiagram.types_map, label_equiv]
  rw [show (OrdinaryResolutionPairs.projection.map k).1.unop = k.1.unop.base by rfl,
    show (OrdinaryResolutionPairs.projection.map k).2 = k.2.unop.base.unop by rfl]
  change (sourceIso Q S n.unop).inv ≫
      Q.map (k.1.unop.diagram.app n.unop ≫ f ≫ (k.2.unop.diagram.app n.unop).unop) ≫
        (targetIso Q S n.unop).inv = _
  rw [Q.map_comp, Q.map_comp]
  have hs := congr_app k.1.unop.over n.unop
  have ht := congrArg Quiver.Hom.unop (congr_app k.2.unop.over n.unop)
  change k.1.unop.diagram.app n.unop ≫ source R n.unop =
    source S n.unop ≫ k.1.unop.base at hs
  change target R n.unop ≫ (k.2.unop.diagram.app n.unop).unop =
    k.2.unop.base.unop ≫ target S n.unop at ht
  have h := fraction_naturality (sourceIso Q R n.unop) (sourceIso Q S n.unop)
    (targetIso Q R n.unop) (targetIso Q S n.unop)
    (Q.map (k.1.unop.diagram.app n.unop)) (Q.map (k.2.unop.diagram.app n.unop).unop)
    (Q.map k.1.unop.base) (Q.map k.2.unop.base.unop) (Q.map f)
    (by
      change Q.map _ ≫ Q.map _ = Q.map _ ≫ Q.map _
      simpa only [Q.map_comp] using congrArg Q.map hs)
    (by
      change Q.map _ ≫ Q.map _ = Q.map _ ≫ Q.map _
      simpa only [Q.map_comp] using congrArg Q.map ht)
  simpa only [Category.assoc] using h

def comparison : OrdinaryResolutionPairs.raw (C := C) ⟶
    OrdinaryResolutionPairs.projection ⋙ LocalizedHomDiagram.spaces Q where
  app R :=
    { app n := ↾(label Q R n)
      naturality {_ _} θ := by
        apply ConcreteCategory.hom_ext
        intro f
        exact label_operator Q R θ f }
  naturality {_ _} k := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro f
    exact label_base Q k n f

end SerrePositivity.HomotopyFunctionComplex.OrdinaryMappingClassLabel
