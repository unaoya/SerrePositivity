module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.AdjunctionHomTriangles

/-!
# 局所化の比較による随伴の三角恒等式

## 概要
HA §1.3.4 の導来随伴を構成するとき、指定された単位・余単位の三角恒等式を照合する。

## 方針
左の三角は左比較が可逆な源に制限し、右の三角は右比較の可逆性を使う。

## 規約
三角恒等式は関手 ∞ 圏のホモトピー圏の射として検証する。

## 使われ方
Barratt–Eccles 代数の底変更随伴。
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory Bicategory SSet
open SerrePositivity.InfinityCategories

local instance localizedAdjunctionTrianglesHomCategory (X Y : QCat.{u}) : Category.{u} (X ⟶ Y) :=
  QCat.bicategory.homCategory X Y

variable {A B C D A₀ : QCat.{u}}

lemma qcat_comp_whiskerLeft {X Y Z W : QCat.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) {h k : Z ⟶ W} (t : h ⟶ k) :
    (f ≫ g) ◁ t = f ◁ (g ◁ t) := by
  simpa only [Strict.associator_eqToIso, eqToIso.hom, eqToIso.inv, eqToHom_refl,
    Category.id_comp, Category.comp_id] using comp_whiskerLeft f g t

lemma qcat_whiskerRight_comp {X Y Z W : QCat.{u}}
    {f g : X ⟶ Y} (t : f ⟶ g) (h : Y ⟶ Z) (k : Z ⟶ W) :
    t ▷ (h ≫ k) = (t ▷ h) ▷ k := by
  simpa only [Strict.associator_eqToIso, eqToIso.hom, eqToIso.inv, eqToHom_refl,
    Category.id_comp, Category.comp_id] using whiskerRight_comp t h k

lemma qcat_whisker_assoc {X Y Z W : QCat.{u}}
    (f : X ⟶ Y) {g h : Y ⟶ Z} (t : g ⟶ h) (k : Z ⟶ W) :
    (f ◁ t) ▷ k = f ◁ (t ▷ k) := by
  simpa only [Strict.associator_eqToIso, eqToIso.hom, eqToIso.inv, eqToHom_refl,
    Category.id_comp, Category.comp_id] using whisker_assoc f t k

variable {F : A ⟶ B} {G : B ⟶ A} {L : C ⟶ D} {R : D ⟶ C}
  (a : Bicategory.Adjunction F G) (q : A ⟶ C) (r : B ⟶ D) (i : A₀ ⟶ A)
  (α : q ≫ L ⟶ F ≫ r) (β : r ≫ R ≅ G ≫ q)
  (η : 𝟙 C ⟶ L ≫ R) (ε : R ≫ L ⟶ 𝟙 D)

variable
  (hη : q ◁ η ≫ α ▷ R ≫ F ◁ β.hom = a.unit ▷ q)
  (hε : r ◁ ε = β.hom ▷ L ≫ G ◁ α ≫ a.counit ▷ r)

set_option maxHeartbeats 600000 in
-- 二つの関手圏で whiskering の端点を合わせる。
/-- 局所化源上の単位・余単位の式から、導来随伴の三角恒等式を得る。 -/
def adjunctionOfLocalizationComparisons
    (hleft : (Bicategory.precomp D (i ≫ q)).Faithful)
    (hright : (Bicategory.precomp C r).Faithful)
    [Mono (i ◁ α)] : Bicategory.Adjunction L R where
  unit := η
  counit := ε
  left_triangle := by
    have ha : a.unit ▷ F ≫ F ◁ a.counit = 𝟙 F := by
      have h := a.left_triangle
      simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.bicategory_leftZigzag_explicit, Strict.associator_eqToIso,
        Strict.leftUnitor_eqToIso,
        Strict.rightUnitor_eqToIso, eqToIso.hom, eqToIso.inv, eqToHom_refl,
        Category.id_comp, Category.comp_id] at h
      exact h
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.bicategory_leftZigzag_explicit, Strict.associator_eqToIso,
        Strict.leftUnitor_eqToIso,
      Strict.rightUnitor_eqToIso, eqToIso.hom, eqToIso.inv, eqToHom_refl,
      Category.id_comp, Category.comp_id]
    apply hleft.map_injective
    change (i ≫ q) ◁ (η ▷ L ≫ L ◁ ε) = (i ≫ q) ◁ 𝟙 L
    apply (cancel_mono (i ◁ α)).mp
    simp only [whiskerLeft_id, qcat_comp_whiskerLeft, ← whiskerLeft_comp]
    rw [show 𝟙 ((i ≫ q) ≫ L) ≫ i ◁ α = i ◁ α from Category.id_comp _]
    apply congrArg (fun k => i ◁ k)
    calc
      (q ◁ (η ▷ L ≫ L ◁ ε)) ≫ α
          = (q ◁ η) ▷ L ≫ (α ▷ R) ▷ L ≫ F ◁ (r ◁ ε) := by
        simp only [whiskerLeft_comp, ← qcat_whisker_assoc, Category.assoc]
        have h := whisker_exchange α ε
        simpa only [qcat_comp_whiskerLeft, qcat_whiskerRight_comp, Strict.rightUnitor_eqToIso,
          eqToIso.hom, eqToIso.inv, eqToHom_refl, Category.id_comp, Category.comp_id,
          whiskerRight_id] using congrArg (fun k => (q ◁ η) ▷ L ≫ k) h
      _ = (a.unit ▷ q) ▷ L ≫ (F ≫ G) ◁ α ≫ F ◁ (a.counit ▷ r) := by
        rw [hε, whiskerLeft_comp, whiskerLeft_comp, ← qcat_whisker_assoc,
          ← qcat_comp_whiskerLeft]
        have hη' : (q ◁ η ≫ α ▷ R) ≫ F ◁ β.hom = a.unit ▷ q :=
          (Category.assoc _ _ _).trans hη
        rw [← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc, hη']
      _ = α ≫ (a.unit ▷ F ≫ F ◁ a.counit) ▷ r := by
        rw [← qcat_whiskerRight_comp, ← whisker_exchange_assoc a.unit α]
        simp only [Strict.leftUnitor_eqToIso, eqToIso.hom, eqToIso.inv, eqToHom_refl,
          Category.id_comp, Category.comp_id, id_whiskerLeft, comp_whiskerRight,
          qcat_whiskerRight_comp, qcat_whisker_assoc]
      _ = α := by
        rw [ha]
        exact (congrArg (fun k => α ≫ k) (id_whiskerRight F r)).trans (Category.comp_id _)
  right_triangle := by
    have ha : G ◁ a.unit ≫ a.counit ▷ G = 𝟙 G := by
      have h := a.right_triangle
      simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.bicategory_rightZigzag_explicit, Strict.associator_eqToIso,
        Strict.leftUnitor_eqToIso,
        Strict.rightUnitor_eqToIso, eqToIso.hom, eqToIso.inv, eqToHom_refl,
        Category.id_comp, Category.comp_id] at h
      exact h
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.bicategory_rightZigzag_explicit, Strict.associator_eqToIso,
        Strict.leftUnitor_eqToIso,
      Strict.rightUnitor_eqToIso, eqToIso.hom, eqToIso.inv, eqToHom_refl,
      Category.id_comp, Category.comp_id]
    apply hright.map_injective
    change r ◁ (R ◁ η ≫ ε ▷ R) = r ◁ 𝟙 R
    apply (cancel_mono β.hom).mp
    simp only [whiskerLeft_id, whiskerLeft_comp, ← qcat_whisker_assoc, hε]
    rw [show 𝟙 (r ≫ R) ≫ β.hom = β.hom from Category.id_comp _]
    simp only [comp_whiskerRight, Category.assoc]
    have hβ := whisker_exchange β.hom η
    have hεβ := whisker_exchange a.counit β.hom
    simp only [id_whiskerLeft, Strict.leftUnitor_eqToIso, eqToIso.hom, eqToIso.inv,
      eqToHom_refl, Category.id_comp, Category.comp_id, qcat_comp_whiskerLeft,
      qcat_whiskerRight_comp] at hεβ
    simp only [qcat_comp_whiskerLeft, qcat_whiskerRight_comp, whiskerRight_id,
      Strict.rightUnitor_eqToIso, eqToIso.hom, eqToIso.inv, eqToHom_refl,
      Category.id_comp, Category.comp_id] at hβ
    rw [reassoc_of% hβ, ← hεβ, qcat_whisker_assoc G α R]
    have hη' : (q ◁ η ≫ α ▷ R) ≫ F ◁ β.hom = a.unit ▷ q :=
      (Category.assoc _ _ _).trans hη
    rw [← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc, hη',
      ← qcat_whisker_assoc, ← comp_whiskerRight, ha]
    exact (congrArg (fun k => β.hom ≫ k) (id_whiskerRight G q)).trans (Category.comp_id _)

end SerrePositivity.EInfinity
