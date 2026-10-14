module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Whiskering

/-! # テンソル作用の自然比較による結同比較の移送 -/

@[expose] public section

universe v₁ v₂ u₁ u₂

noncomputable section

namespace SerrePositivity.TensorActionTransport

open CategoryTheory CategoryTheory.MonoidalCategory

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [MonoidalCategory V] [MonoidalCategory C]
  (F : V ⥤ C) (H : V ⥤ C ⥤ C) (e : F ⋙ curriedTensor C ≅ H)
  (μ : ∀ X Y : V, F.obj X ⊗ F.obj Y ≅ F.obj (X ⊗ Y))

/-- 二つの作用の反復とパラメータの積との結合自然比較。 -/
def associatorNatIso (X Y : V) : H.obj (X ⊗ Y) ≅ H.obj Y ⋙ H.obj X :=
  (e.app (X ⊗ Y)).symm ≪≫ (curriedTensor C).mapIso (μ X Y).symm ≪≫
    tensorLeftTensor (F.obj X) (F.obj Y) ≪≫
      CategoryTheory.Functor.isoWhiskerRight (e.app Y) (tensorLeft (F.obj X)) ≪≫
        CategoryTheory.Functor.isoWhiskerLeft (H.obj Y) (e.app X)

/-- 移送した結同比較の順射の公式。 -/
lemma associator_hom (X Y : V) (A : C) :
    (associatorNatIso F H e μ X Y).hom.app A =
      (e.inv.app (X ⊗ Y)).app A ≫ (μ X Y).inv ▷ A ≫
        (α_ (F.obj X) (F.obj Y) A).hom ≫
          F.obj X ◁ (e.hom.app Y).app A ≫ (e.hom.app X).app ((H.obj Y).obj A) := rfl

omit [MonoidalCategory V] in
/-- 作用の比較のパラメータに関する自然性。 -/
@[reassoc]
lemma comparison_naturality {X Y : V} (f : X ⟶ Y) (A : C) :
    F.map f ▷ A ≫ (e.hom.app Y).app A =
      (e.hom.app X).app A ≫ (H.map f).app A :=
  congrArg (fun k => k.app A) (e.hom.naturality f)

omit [MonoidalCategory V] in
/-- 作用の逆比較のパラメータに関する自然性。 -/
@[reassoc]
lemma comparison_inv_naturality {X Y : V} (f : X ⟶ Y) (A : C) :
    (H.map f).app A ≫ (e.inv.app Y).app A =
      (e.inv.app X).app A ≫ F.map f ▷ A :=
  congrArg (fun k => k.app A) (e.inv.naturality f)

/-- 積の比較の順射の自然性から逆射の自然性を得る。 -/
lemma tensorComparison_inv_naturality {X X' Y Y' : V} (f : X ⟶ X') (g : Y ⟶ Y')
    (hμ : (F.map f ⊗ₘ F.map g) ≫ (μ X' Y').hom =
      (μ X Y).hom ≫ F.map (f ⊗ₘ g)) :
    F.map (f ⊗ₘ g) ≫ (μ X' Y').inv = (μ X Y).inv ≫ (F.map f ⊗ₘ F.map g) := by
  apply (cancel_mono (μ X' Y').hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hμ, Iso.inv_hom_id_assoc]

/-- 結同比較のパラメータの両変数に関する自然性の法則。 -/
def associatorParameterLaw {X X' Y Y' : V} (f : X ⟶ X') (g : Y ⟶ Y') (A : C) : Prop :=
  (H.map (f ⊗ₘ g)).app A ≫ (associatorNatIso F H e μ X' Y').hom.app A =
    (associatorNatIso F H e μ X Y).hom.app A ≫
      (H.map f).app ((H.obj Y).obj A) ≫ (H.obj X').map ((H.map g).app A)

/-- 積の比較が自然なら、作用へ移した結同比較もパラメータの両変数に自然。 -/
lemma associator_parameter_naturality {X X' Y Y' : V} (f : X ⟶ X') (g : Y ⟶ Y') (A : C)
    (hμ : F.map (f ⊗ₘ g) ≫ (μ X' Y').inv =
      (μ X Y).inv ≫ (F.map f ⊗ₘ F.map g)) :
    associatorParameterLaw F H e μ f g A := by
  unfold associatorParameterLaw
  rw [associator_hom, associator_hom]
  simp only [Category.assoc]
  rw [comparison_inv_naturality_assoc]
  rw [← comp_whiskerRight_assoc, hμ, comp_whiskerRight]
  simp only [Category.assoc]
  have ha := associator_naturality (F.map f) (F.map g) (𝟙 A)
  rw [tensorHom_id, tensorHom_id] at ha
  rw [tensorHom_def (F.map f) (F.map g ▷ A)] at ha
  rw [reassoc_of% ha]
  rw [← whiskerLeft_comp_assoc, comparison_naturality, whiskerLeft_comp]
  simp only [Category.assoc]
  rw [← whisker_exchange_assoc]
  have hv := (e.hom.app X').naturality ((H.map g).app A)
  change F.obj X' ◁ (H.map g).app A ≫ (e.hom.app X').app ((H.obj Y').obj A) =
    (e.hom.app X').app ((H.obj Y).obj A) ≫ (H.obj X').map ((H.map g).app A) at hv
  rw [hv, comparison_naturality_assoc]

/-- 積の順比較の自然性から、作用の結同比較の自然性を得る。 -/
lemma associator_parameter_naturality_of_hom {X X' Y Y' : V}
    (f : X ⟶ X') (g : Y ⟶ Y') (A : C)
    (hμ : (F.map f ⊗ₘ F.map g) ≫ (μ X' Y').hom =
      (μ X Y).hom ≫ F.map (f ⊗ₘ g)) :
    associatorParameterLaw F H e μ f g A :=
  associator_parameter_naturality F H e μ f g A
    (tensorComparison_inv_naturality F μ f g hμ)

/-- 作用の結同比較の三変数に関する自然性の法則。 -/
def associatorNaturalityLaw {X X' Y Y' : V} (f : X ⟶ X') (g : Y ⟶ Y')
    {A B : C} (h : A ⟶ B) : Prop :=
  (H.map (f ⊗ₘ g)).app A ≫ (H.obj (X' ⊗ Y')).map h ≫
      (associatorNatIso F H e μ X' Y').hom.app B =
    (associatorNatIso F H e μ X Y).hom.app A ≫
      (H.map f).app ((H.obj Y).obj A) ≫ (H.obj X').map ((H.map g).app A) ≫
        (H.obj Y' ⋙ H.obj X').map h

/-- パラメータの自然性と値域の自然性を、三変数の自然性へまとめる。 -/
lemma associator_naturality {X X' Y Y' : V} (f : X ⟶ X') (g : Y ⟶ Y')
    {A B : C} (h : A ⟶ B)
    (hμ : (F.map f ⊗ₘ F.map g) ≫ (μ X' Y').hom =
      (μ X Y).hom ≫ F.map (f ⊗ₘ g)) :
    associatorNaturalityLaw F H e μ f g h := by
  unfold associatorNaturalityLaw
  rw [(associatorNatIso F H e μ X' Y').hom.naturality h]
  have hp := associator_parameter_naturality_of_hom F H e μ f g A hμ
  unfold associatorParameterLaw at hp
  rw [← Category.assoc, hp]
  simp only [Category.assoc]

end SerrePositivity.TensorActionTransport
