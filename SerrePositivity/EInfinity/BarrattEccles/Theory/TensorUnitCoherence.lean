module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.HadamardCoherence
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# テンソルの二列分離と単位子

## 概要
BF §1.1.4 のテンソル単位の作用を縮約する一般のモノイダル図式。

## 方針
単位対象との交換を単位子で表し、モノイダル整合性へ帰着する。

## 規約
対称モノイダル圏の任意の二対象で述べ、複体の次数を展開しない。

## 使われ方
HA 3.2.4.7 の余積比較で使うテンソル代数の左右の単位同型。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- BF §1.1.4 の右単位の分離の縮約。 -/
@[reassoc]
lemma tensorUnitRightAssembly (V N : C) :
    tensorμ V (𝟙_ C) N (𝟙_ C) ≫
      ((V ⊗ N) ◁ (λ_ (𝟙_ C)).hom) ≫ (ρ_ (V ⊗ N)).hom =
      (ρ_ V).hom ⊗ₘ (ρ_ N).hom := by
  simp only [tensorμ, braiding_tensorUnit_left, comp_whiskerRight,
    whiskerLeft_comp, Category.assoc]
  monoidal

/-- BF §1.1.4 の左単位の分離の縮約。 -/
@[reassoc]
lemma tensorUnitLeftAssembly (V N : C) :
    tensorμ (𝟙_ C) V (𝟙_ C) N ≫
      ((λ_ (𝟙_ C)).hom ▷ (V ⊗ N)) ≫ (λ_ (V ⊗ N)).hom =
      (λ_ V).hom ⊗ₘ (λ_ N).hom := by
  simp only [tensorμ, braiding_tensorUnit_right, comp_whiskerRight,
    whiskerLeft_comp, Category.assoc]
  monoidal

/-- BF §1.1.4 の右余単位を係数で縮約する。 -/
@[reassoc]
lemma tensorUnitRightCoefficient (O N : C) :
    ((ρ_ O).inv ▷ (N ⊗ 𝟙_ C)) ≫ tensorμ O (𝟙_ C) N (𝟙_ C) ≫
      ((O ⊗ N) ◁ (λ_ (𝟙_ C)).hom) ≫ (ρ_ (O ⊗ N)).hom = O ◁ (ρ_ N).hom := by
  rw [tensorUnitRightAssembly, whiskerRight_comp_tensorHom, Iso.inv_hom_id, id_tensorHom]

/-- BF §1.1.4 の左余単位を係数で縮約する。 -/
@[reassoc]
lemma tensorUnitLeftCoefficient (O N : C) :
    ((λ_ O).inv ▷ (𝟙_ C ⊗ N)) ≫ tensorμ (𝟙_ C) O (𝟙_ C) N ≫
      ((λ_ (𝟙_ C)).hom ▷ (O ⊗ N)) ≫ (λ_ (O ⊗ N)).hom = O ◁ (λ_ N).hom := by
  rw [tensorUnitLeftAssembly, whiskerRight_comp_tensorHom, Iso.inv_hom_id, id_tensorHom]

/-- BF §1.1.4 の右単位の縮約は任意の作用射で自然。 -/
lemma tensorUnitRightAction {O M N V : C} (s : M ⟶ N ⊗ 𝟙_ C) (a : O ⊗ N ⟶ V) :
    ((ρ_ O).inv ⊗ₘ s) ≫ tensorμ O (𝟙_ C) N (𝟙_ C) ≫
      (a ⊗ₘ (λ_ (𝟙_ C)).hom) ≫ (ρ_ V).hom =
      (O ◁ (s ≫ (ρ_ N).hom)) ≫ a := by
  rw [tensorHom_def' (ρ_ O).inv s, tensorHom_def' a (λ_ (𝟙_ C)).hom]
  simp only [Category.assoc]
  rw [rightUnitor_naturality, tensorUnitRightCoefficient_assoc, ← whiskerLeft_comp_assoc]

/-- BF §1.1.4 の左単位の縮約は任意の作用射で自然。 -/
lemma tensorUnitLeftAction {O M N V : C} (s : M ⟶ 𝟙_ C ⊗ N) (a : O ⊗ N ⟶ V) :
    ((λ_ O).inv ⊗ₘ s) ≫ tensorμ (𝟙_ C) O (𝟙_ C) N ≫
      ((λ_ (𝟙_ C)).hom ⊗ₘ a) ≫ (λ_ V).hom =
      (O ◁ (s ≫ (λ_ N).hom)) ≫ a := by
  rw [tensorHom_def' (λ_ O).inv s, tensorHom_def (λ_ (𝟙_ C)).hom a]
  simp only [Category.assoc]
  rw [leftUnitor_naturality, tensorUnitLeftCoefficient_assoc, ← whiskerLeft_comp_assoc]

/-- BF §1.1.4 の右余単位と二列の作用の縮約。 -/
lemma tensorActionRightCounit {O M N T V : C} (d : O ⟶ O ⊗ O) (e : O ⟶ 𝟙_ C)
    (s : M ⟶ N ⊗ T) (a : O ⊗ N ⟶ V) (t : T ⟶ 𝟙_ C)
    (hd : d ≫ (O ◁ e) ≫ (ρ_ O).hom = 𝟙 O) :
    (d ⊗ₘ s) ≫ tensorμ O O N T ≫
      (a ⊗ₘ ((e ▷ T) ≫ (λ_ T).hom ≫ t)) ≫ (ρ_ V).hom =
      (O ◁ (s ≫ (N ◁ t) ≫ (ρ_ N).hom)) ≫ a := by
  have he : (e ▷ T) ≫ (λ_ T).hom ≫ t = (e ⊗ₘ t) ≫ (λ_ (𝟙_ C)).hom := by
    rw [← leftUnitor_naturality, ← tensorHom_def_assoc]
  have hd' : d ≫ (O ◁ e) = (ρ_ O).inv := by
    apply (cancel_mono (ρ_ O).hom).mp
    rw [Category.assoc, hd, Iso.inv_hom_id]
  have hm := tensorμ_natural (𝟙 O) e (𝟙 N) t
  simp only [tensorHom_id, id_whiskerRight, id_tensorHom] at hm
  rw [he, ← whiskerLeft_comp_tensorHom_assoc, ← reassoc_of% hm,
    tensorHom_comp_tensorHom_assoc, hd', tensorUnitRightAction]
  simp only [Category.assoc]

/-- BF §1.1.4 の左余単位と二列の作用の縮約。 -/
lemma tensorActionLeftCounit {O M N T V : C} (d : O ⟶ O ⊗ O) (e : O ⟶ 𝟙_ C)
    (s : M ⟶ T ⊗ N) (a : O ⊗ N ⟶ V) (t : T ⟶ 𝟙_ C)
    (hd : d ≫ (e ▷ O) ≫ (λ_ O).hom = 𝟙 O) :
    (d ⊗ₘ s) ≫ tensorμ O O T N ≫
      (((e ▷ T) ≫ (λ_ T).hom ≫ t) ⊗ₘ a) ≫ (λ_ V).hom =
      (O ◁ (s ≫ (t ▷ N) ≫ (λ_ N).hom)) ≫ a := by
  have he : (e ▷ T) ≫ (λ_ T).hom ≫ t = (e ⊗ₘ t) ≫ (λ_ (𝟙_ C)).hom := by
    rw [← leftUnitor_naturality, ← tensorHom_def_assoc]
  have hd' : d ≫ (e ▷ O) = (λ_ O).inv := by
    apply (cancel_mono (λ_ O).hom).mp
    rw [Category.assoc, hd, Iso.inv_hom_id]
  have hm := tensorμ_natural e (𝟙 O) t (𝟙 N)
  simp only [tensorHom_id, id_whiskerRight] at hm
  rw [he, ← whiskerRight_comp_tensorHom_assoc, ← reassoc_of% hm,
    tensorHom_comp_tensorHom_assoc, hd', tensorUnitLeftAction]
  simp only [Category.assoc]

end SerrePositivity.EInfinity
