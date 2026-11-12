module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import Mathlib.CategoryTheory.Enriched.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
概要：豊穣圏のパラメータ付き可換正方形の合成。
方針：三つの写像族の結合律で中間の族を移し、braiding の六角形を使う。
規約：特定の写像空間・Kan 性を仮定しない。
使われ方：cotensor の普遍評価と可換な射の組の合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory
namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.Spectra
variable (V : Type u) [Category.{v} V] [MonoidalCategory V]
  {C : Type w} [EnrichedCategory V C]

/-- 三つの独立なパラメータで表した豊穣結合律。 -/
@[reassoc]
lemma enriched_parameter_assoc {P Q R : V} {W X Y Z : C}
    (a : P ⟶ (W ⟶[V] X)) (b : Q ⟶ (X ⟶[V] Y)) (c : R ⟶ (Y ⟶[V] Z)) :
    (α_ P Q R).inv ≫ (((a ⊗ₘ b) ≫ eComp V W X Y) ⊗ₘ c) ≫ eComp V W Y Z =
      (a ⊗ₘ ((b ⊗ₘ c) ≫ eComp V X Y Z)) ≫ eComp V W X Z := by
  rw [← tensorHom_comp_whiskerRight, Category.assoc,
    ← associator_inv_naturality_assoc, e_assoc, ← tensorHom_comp_whiskerLeft_assoc]

/-- 左に括った三つの族の合成を、右に括った式へ移す。 -/
@[reassoc]
lemma enriched_parameter_assoc_hom {P Q R : V} {W X Y Z : C}
    (a : P ⟶ (W ⟶[V] X)) (b : Q ⟶ (X ⟶[V] Y)) (c : R ⟶ (Y ⟶[V] Z)) :
    (((a ⊗ₘ b) ≫ eComp V W X Y) ⊗ₘ c) ≫ eComp V W Y Z =
      (α_ P Q R).hom ≫ (a ⊗ₘ ((b ⊗ₘ c) ≫ eComp V X Y Z)) ≫ eComp V W X Z := by
  have h := congrArg (fun f ↦ (α_ P Q R).hom ≫ f) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_parameter_assoc V a b c)
  simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] using h

variable [BraidedCategory V]
/-- 共通のパラメータを持つ二つの豊穣可換正方形は合成できる。 -/
lemma enriched_parameter_square_comp {A P Q : V} {X Y Z X' Y' Z' : C}
    (ex : A ⟶ (X' ⟶[V] X)) (ey : A ⟶ (Y' ⟶[V] Y)) (ez : A ⟶ (Z' ⟶[V] Z))
    (a : P ⟶ (X ⟶[V] Y)) (a' : P ⟶ (X' ⟶[V] Y'))
    (b : Q ⟶ (Y ⟶[V] Z)) (b' : Q ⟶ (Y' ⟶[V] Z'))
    (ha : (ex ⊗ₘ a) ≫ eComp V X' X Y =
      (β_ A P).hom ≫ (a' ⊗ₘ ey) ≫ eComp V X' Y' Y)
    (hb : (ey ⊗ₘ b) ≫ eComp V Y' Y Z =
      (β_ A Q).hom ≫ (b' ⊗ₘ ez) ≫ eComp V Y' Z' Z) :
    (ex ⊗ₘ ((a ⊗ₘ b) ≫ eComp V X Y Z)) ≫ eComp V X' X Z =
      (β_ A (P ⊗ Q)).hom ≫
        (((a' ⊗ₘ b') ≫ eComp V X' Y' Z') ⊗ₘ ez) ≫ eComp V X' Z' Z := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_parameter_assoc V ex a b, ha,
    ← whiskerRight_comp_tensorHom_assoc, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_parameter_assoc_hom V a' ey b,
    hb, ← whiskerLeft_comp_tensorHom_assoc, ← _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_parameter_assoc V a' b' ez]
  rw [BraidedCategory.braiding_tensor_right_hom]
  simp only [Category.assoc]

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.enriched_parameter_assoc := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_parameter_assoc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.enriched_parameter_assoc_assoc := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_parameter_assoc_assoc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.enriched_parameter_assoc_hom := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_parameter_assoc_hom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.enriched_parameter_assoc_hom_assoc := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_parameter_assoc_hom_assoc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.enriched_parameter_square_comp := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_parameter_square_comp
