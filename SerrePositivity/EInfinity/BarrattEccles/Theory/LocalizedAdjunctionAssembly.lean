module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.LocalizedAdjunctionTriangles

/-!
# 局所化に沿う随伴の単位と余単位の構成

## 概要
HA §1.3.4 の導来随伴に用いる局所化と比較の組み立て。

## 方針
左の比較が可逆な源で単位を降ろし、右の全源で余単位を降ろす。

## 規約
元の随伴の二胞体と同じ置換の augmentation を使う。

## 使われ方
Barratt–Eccles の底変更の導来随伴。
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory Bicategory SSet

local instance localizedAdjunctionAssemblyHomCategory (X Y : QCat.{u}) : Category.{u} (X ⟶ Y) :=
  QCat.bicategory.homCategory X Y

variable {A B C D A₀ : QCat.{u}}
  {F : A ⟶ B} {G : B ⟶ A} {L : C ⟶ D} {R : D ⟶ C}
  (a : Bicategory.Adjunction F G) (q : A ⟶ C) (r : B ⟶ D) (i : A₀ ⟶ A)
  (α : q ≫ L ⟶ F ≫ r) (β : r ≫ R ≅ G ≫ q)

/-- 始域が置換を反転するとき、二胞体の等式は置換の像で検証できる。 -/
lemma qcatPrecomp_injective_of_augmentation {Z : QCat.{u}} {U V : A ⟶ Z}
    (p : A ⟶ A₀) (w : p ≫ i ⟶ 𝟙 A) [Epi (w ▷ U)] {x y : U ⟶ V}
    (h : i ◁ x = i ◁ y) : x = y := by
  apply (cancel_epi (w ▷ U)).mp
  have hx := whisker_exchange w x
  have hy := whisker_exchange w y
  simp only [qcat_comp_whiskerLeft, id_whiskerLeft, Strict.leftUnitor_eqToIso,
    eqToIso.hom, eqToIso.inv, eqToHom_refl, Category.id_comp, Category.comp_id] at hx hy
  rw [← hx, ← hy, h]

/-- 局所化源の充満忠実性から指定された導来随伴を構成する。 -/
def adjunctionFromLocalization
    (p : A ⟶ A₀) (w : p ≫ i ⟶ 𝟙 A) [IsIso (w ▷ q)]
    [IsIso (i ◁ α)]
    (h₀ : (Bicategory.precomp C (i ≫ q)).FullyFaithful)
    (h₁ : (Bicategory.precomp C r).FullyFaithful)
    (h₂ : (Bicategory.precomp D r).FullyFaithful)
    (h₃ : (Bicategory.precomp D (i ≫ q)).FullyFaithful) :
    Bicategory.Adjunction L R := by
  let u : (i ≫ q) ≫ 𝟙 C ⟶ (i ≫ q) ≫ (L ≫ R) :=
    (i ◁ a.unit) ▷ q ≫ (i ≫ F) ◁ β.inv ≫ inv (i ◁ α) ▷ R
  let v : r ≫ (R ≫ L) ⟶ r ≫ 𝟙 D := β.hom ▷ L ≫ G ◁ α ≫ a.counit ▷ r
  let η := h₀.preimage u
  let ε := h₂.preimage v
  have hu : (i ≫ q) ◁ η = u := h₀.map_preimage u
  have hv : r ◁ ε = v := h₂.map_preimage v
  have hη : q ◁ η ≫ α ▷ R ≫ F ◁ β.hom = a.unit ▷ q := by
    have : Epi (w ▷ (q ≫ 𝟙 C)) := by
      change Epi (w ▷ q)
      infer_instance
    apply qcatPrecomp_injective_of_augmentation i p w
    simp only [whiskerLeft_comp, ← qcat_comp_whiskerLeft, ← qcat_whisker_assoc, hu, u]
    have hα := (whiskerRightIso (asIso (i ◁ α)) R).inv_hom_id
    change inv (i ◁ α) ▷ R ≫ (i ◁ α) ▷ R = 𝟙 _ at hα
    have hβ := (whiskerLeftIso (i ≫ F) β).inv_hom_id
    change (i ≫ F) ◁ β.inv ≫ (i ≫ F) ◁ β.hom = 𝟙 _ at hβ
    simp only [Category.assoc, reassoc_of% hα, hβ]
    exact Category.comp_id ((i ◁ a.unit) ▷ q)
  exact adjunctionOfLocalizationComparisons a q r i α β η ε hη hv h₃.faithful h₁.faithful

end SerrePositivity.EInfinity
