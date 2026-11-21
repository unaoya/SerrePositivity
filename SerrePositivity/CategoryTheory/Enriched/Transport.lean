module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Enriched.Basic
public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
public import Mathlib.CategoryTheory.Whiskering

/-!
# Enriched.Transport

## 概要
関連する圏論の構成と補題をまとめる。各構成の詳細は以下の元モジュールの説明を参照。

## 方針
元の宣言と証明を保持し、依存順に section を分けて配置する。

## 規約
公開宣言名・名前空間・宇宙変数の意味を変更しない。元の module docstring は各節に保存する。

## 使われ方
旧モジュールの利用元は `SerrePositivity.CategoryTheory.Enriched.Transport` を直接 import する。
-/

/-! ## LaxPointHom（旧 SerrePositivity/CategoryTheory/Monoidal/LaxPointHom.lean） -/

/-! # lax monoidal関手による単位からの射の移送 -/

@[expose] public section LaxPointHom
universe v₁ v₂ u₁ u₂

namespace SerrePositivity.LaxPointHom

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Functor.LaxMonoidal

variable {V : Type u₁} {W : Type u₂} [Category.{v₁} V] [Category.{v₂} W]
  [MonoidalCategory V] [MonoidalCategory W] (F : V ⥤ W) [F.LaxMonoidal]

/-- 関手の単位比較を使って単位からの射を送る。 -/
def map {X : V} (f : 𝟙_ V ⟶ X) : 𝟙_ W ⟶ F.obj X := ε F ≫ F.map f

lemma left_action {X Y Z : V} (f : 𝟙_ V ⟶ X) (m : X ⊗ Y ⟶ Z) :
    (λ_ (F.obj Y)).inv ≫ map F f ▷ F.obj Y ≫ μ F X Y ≫ F.map m =
      F.map ((λ_ Y).inv ≫ f ▷ Y ≫ m) := by
  unfold map
  rw [comp_whiskerRight]
  simp only [Category.assoc]
  rw [μ_natural_left_assoc, left_unitality_inv_assoc]
  simp only [F.map_comp]

lemma right_action {X Y Z : V} (f : 𝟙_ V ⟶ Y) (m : X ⊗ Y ⟶ Z) :
    (ρ_ (F.obj X)).inv ≫ F.obj X ◁ map F f ≫ μ F X Y ≫ F.map m =
      F.map ((ρ_ X).inv ≫ X ◁ f ≫ m) := by
  unfold map
  rw [whiskerLeft_comp]
  simp only [Category.assoc]
  rw [μ_natural_right_assoc, right_unitality_inv_assoc]
  simp only [F.map_comp]

/-- 単位からの二つの射の合成はlax monoidalの比較と両立する。 -/
lemma composition {X Y Z : V} (f : 𝟙_ V ⟶ X) (g : 𝟙_ V ⟶ Y) (m : X ⊗ Y ⟶ Z) :
    (λ_ (𝟙_ W)).inv ≫ (map F f ⊗ₘ map F g) ≫ μ F X Y ≫ F.map m =
      map F ((λ_ (𝟙_ V)).inv ≫ (f ⊗ₘ g) ≫ m) := by
  unfold map
  rw [← tensorHom_comp_tensorHom]
  simp only [Category.assoc]
  rw [μ_natural_assoc]
  rw [tensorHom_def']
  simp only [Category.assoc]
  rw [← leftUnitor_inv_naturality_assoc, left_unitality_inv_assoc]
  rw [← F.map_comp, ← F.map_comp]

end SerrePositivity.LaxPointHom

end LaxPointHom

/-! ## ReverseComposition（旧 SerrePositivity/CategoryTheory/Monoidal/ReverseComposition.lean） -/

/-! # 交換で因子の順序を逆にした合成の法則 -/

@[expose] public section ReverseComposition
universe v u u'

namespace SerrePositivity.ReverseComposition

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory

variable {V : Type u} [Category.{v} V] [MonoidalCategory V] [BraidedCategory V]

/-- 合成の入力の二つの因子の順序を交換する。 -/
def reverse {X Y Z : V} (m : Y ⊗ X ⟶ Z) : X ⊗ Y ⟶ Z := (β_ X Y).hom ≫ m

/-- 三つの因子を逆順へ移す二つの経路は一致する。 -/
lemma reverse_three (X Y Z : V) :
    (α_ X Y Z).inv ≫ (β_ X Y).hom ▷ Z ≫ (β_ (Y ⊗ X) Z).hom =
    X ◁ (β_ Y Z).hom ≫ (β_ X (Z ⊗ Y)).hom ≫ (α_ Z Y X).hom := by
  rw [braiding_tensor_left_hom, braiding_tensor_right_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact yang_baxter X Y Z

/-- 後から適用する射を左因子に置く結合則を、逆順の合成の結合則へ移す。 -/
lemma associativity {A B C D E F : V} (m₁ : B ⊗ A ⟶ D) (m₂ : C ⊗ B ⟶ E)
    (m₃ : C ⊗ D ⟶ F) (m₄ : E ⊗ A ⟶ F)
    (h : m₂ ▷ A ≫ m₄ = (α_ C B A).hom ≫ C ◁ m₁ ≫ m₃) :
    (α_ A B C).inv ≫ reverse m₁ ▷ C ≫ reverse m₃ =
      A ◁ reverse m₂ ≫ reverse m₄ := by
  unfold reverse
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  rw [braiding_naturality_left_assoc, braiding_naturality_right_assoc, h]
  rw [← reassoc_of% (reverse_three A B C)]

/-- 逆順の合成の左単位則は、元の合成の右単位則から得られる。 -/
lemma left_unit {X U : V} (e : 𝟙_ V ⟶ U) (m : X ⊗ U ⟶ X)
    (h : X ◁ e ≫ m = (ρ_ X).hom) :
    (λ_ X).inv ≫ e ▷ X ≫ reverse m = 𝟙 X := by
  unfold reverse
  rw [braiding_naturality_left_assoc, h, braiding_rightUnitor, Iso.inv_hom_id]

/-- 逆順の合成の右単位則は、元の合成の左単位則から得られる。 -/
lemma right_unit {X U : V} (e : 𝟙_ V ⟶ U) (m : U ⊗ X ⟶ X)
    (h : e ▷ X ≫ m = (λ_ X).hom) :
    (ρ_ X).inv ≫ X ◁ e ≫ reverse m = 𝟙 X := by
  unfold reverse
  rw [braiding_naturality_right_assoc, h, braiding_leftUnitor, Iso.inv_hom_id]

/-- 二つの点の合成との一致は、合成の因子を交換しても保たれる。 -/
lemma points {X Y Z : V} (f : 𝟙_ V ⟶ X) (g : 𝟙_ V ⟶ Y) (m : Y ⊗ X ⟶ Z)
    (h : 𝟙_ V ⟶ Z) (hm : (λ_ (𝟙_ V)).inv ≫ (g ⊗ₘ f) ≫ m = h) :
    (λ_ (𝟙_ V)).inv ≫ (f ⊗ₘ g) ≫ reverse m = h := by
  unfold reverse
  rw [braiding_naturality_assoc, reassoc_of% (leftUnitor_inv_braiding (𝟙_ V)),
    ← unitors_inv_equal]
  exact hm

/-- 後から適用する射を左に置く合成から、通常の因子順の豊穣圏を構成する。 -/
@[instance_reducible]
def enrichedCategory (C : Type u') (Hom : C → C → V)
    (e : ∀ X, 𝟙_ V ⟶ Hom X X)
    (m : ∀ X Y Z, Hom Y Z ⊗ Hom X Y ⟶ Hom X Z)
    (hl : ∀ X Y, (e Y ⊗ₘ 𝟙 (Hom X Y)) ≫ m X Y Y = (λ_ (Hom X Y)).hom)
    (hr : ∀ X Y, (𝟙 (Hom X Y) ⊗ₘ e X) ≫ m X X Y = (ρ_ (Hom X Y)).hom)
    (ha : ∀ W X Y Z, (m X Y Z ⊗ₘ 𝟙 (Hom W X)) ≫ m W X Z =
      (α_ (Hom Y Z) (Hom X Y) (Hom W X)).hom ≫
        (𝟙 (Hom Y Z) ⊗ₘ m W X Y) ≫ m W Y Z) : EnrichedCategory V C where
  Hom := Hom
  id := e
  comp X Y Z := reverse (m X Y Z)
  id_comp X Y := by
    apply left_unit (e X) (m X X Y)
    have h := hr X Y
    rw [id_tensorHom] at h
    exact h
  comp_id X Y := by
    apply right_unit (e Y) (m X Y Y)
    have h := hl X Y
    rw [tensorHom_id] at h
    exact h
  assoc W X Y Z := by
    apply associativity (m W X Y) (m X Y Z) (m W Y Z) (m W X Z)
    have h := ha W X Y Z
    rw [tensorHom_id, id_tensorHom] at h
    exact h

end SerrePositivity.ReverseComposition

end ReverseComposition

/-! ## TransportEnrichmentComparisons（旧 SerrePositivity/CategoryTheory/Monoidal/TransportEnrichmentComparisons.lean） -/

/-! # 豊穣構造の移送の合成と単位の比較 -/

@[expose] public section TransportEnrichmentComparisons
universe v₁ v₂ u₁ u₂ u₃

noncomputable section

namespace SerrePositivity.TransportEnrichmentComparisons

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Functor.LaxMonoidal

variable {V : Type u₁} {W : Type u₂} [Category.{v₁} V] [Category.{v₂} W]
  [MonoidalCategory V] [MonoidalCategory W]
  (F : V ⥤ W) (C : Type u₃) [EnrichedCategory V C]

section

variable [F.LaxMonoidal]

/-- lax monoidal関手で移した豊穣構造を元の対象型で扱う。 -/
@[instance_reducible]
def category : EnrichedCategory W C :=
  inferInstanceAs (EnrichedCategory W (TransportEnrichment F C))

/-- 移した豊穣構造の単位と指定した射の一致。 -/
def identityLaw (X : C) (k : 𝟙_ W ⟶ F.obj (X ⟶[V] X)) : Prop :=
  (category F C).id X = k

/-- 元の単位と関手の単位比較から、移送後の単位の一致を得る。 -/
lemma identity_eq (X : C) (e : 𝟙_ V ⟶ (X ⟶[V] X))
    (he : eId V X = e) (k : 𝟙_ W ⟶ F.obj (X ⟶[V] X))
    (hk : ε F ≫ F.map e = k) : identityLaw F C X k := by
  change ε F ≫ F.map (eId V X) = k
  rw [he]
  exact hk

end

variable [BraidedCategory V] [BraidedCategory W] [F.LaxBraided]

/-- 逆順の合成から移した豊穣構造の合成の具体式。 -/
def reverseCompositionLaw (X Y Z : C) (m : (Y ⟶[V] Z) ⊗ (X ⟶[V] Y) ⟶ (X ⟶[V] Z)) :
    Prop :=
  (category F C).comp X Y Z =
    (β_ (F.obj (X ⟶[V] Y)) (F.obj (Y ⟶[V] Z))).hom ≫
      μ F (Y ⟶[V] Z) (X ⟶[V] Y) ≫ F.map m

/-- 交換で逆順にした合成の移送は、交換・関手の比較・元の合成の順に計算できる。 -/
lemma reverse_composition (X Y Z : C)
    (m : (Y ⟶[V] Z) ⊗ (X ⟶[V] Y) ⟶ (X ⟶[V] Z))
    (hm : eComp V X Y Z = ReverseComposition.reverse m) :
    reverseCompositionLaw F C X Y Z m := by
  change μ F _ _ ≫ F.map (eComp V X Y Z) = _
  rw [hm, ReverseComposition.reverse, F.map_comp, ← Category.assoc, Functor.LaxBraided.braided]
  exact Category.assoc _ _ _

end SerrePositivity.TransportEnrichmentComparisons
end

end TransportEnrichmentComparisons

/-! ## TransportOrdinaryEnrichment（旧 SerrePositivity/CategoryTheory/Monoidal/TransportOrdinaryEnrichment.lean） -/

/-! # 単位からの射の同値による通常の豊穣圏の移送 -/

@[expose] public section TransportOrdinaryEnrichment
universe v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

namespace SerrePositivity.TransportOrdinaryEnrichment

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Functor.LaxMonoidal

variable {V : Type u₁} {W : Type u₂} [Category.{v₁} V] [Category.{v₂} W]
  [MonoidalCategory V] [MonoidalCategory W] (F : V ⥤ W) [F.LaxMonoidal]
  (C : Type u₃) [Category.{v₃} C] [EnrichedOrdinaryCategory V C]
  (t : ∀ X : V, (𝟙_ V ⟶ X) ≃ (𝟙_ W ⟶ F.obj X))
  (ht : ∀ X (f : 𝟙_ V ⟶ X), t X f = LaxPointHom.map F f)

/-- 単位からの射の同値を使って既存の圏構造も豊穣構造とともに移す。 -/
@[instance_reducible]
def ordinaryCategory : EnrichedOrdinaryCategory W C where
  toEnrichedCategory := TransportEnrichmentComparisons.category F C
  homEquiv {X Y} := (eHomEquiv V).trans (t (X ⟶[V] Y))
  homEquiv_id X := by
    change t (X ⟶[V] X) (eHomEquiv V (𝟙 X)) = ε F ≫ F.map (eId V X)
    rw [eHomEquiv_id, ht]
    rfl
  homEquiv_comp {X Y Z} f g := by
    change t (X ⟶[V] Z) (eHomEquiv V (f ≫ g)) =
      (λ_ (𝟙_ W)).inv ≫
        (t (X ⟶[V] Y) (eHomEquiv V f) ⊗ₘ t (Y ⟶[V] Z) (eHomEquiv V g)) ≫
          μ F (X ⟶[V] Y) (Y ⟶[V] Z) ≫ F.map (eComp V X Y Z)
    rw [ht, ht, ht, eHomEquiv_comp]
    exact (LaxPointHom.composition F (eHomEquiv V f) (eHomEquiv V g) (eComp V X Y Z)).symm

lemma whiskerRight_map {X X' : C} (f : X ⟶ X') (Y : C) :
    let : EnrichedOrdinaryCategory W C := ordinaryCategory F C t ht
    eHomWhiskerRight W f Y = F.map (eHomWhiskerRight V f Y) := by
  let : EnrichedOrdinaryCategory W C := ordinaryCategory F C t ht
  change (λ_ (F.obj (X' ⟶[V] Y))).inv ≫
    t (X ⟶[V] X') (eHomEquiv V f) ▷ F.obj (X' ⟶[V] Y) ≫
      μ F _ _ ≫ F.map (eComp V X X' Y) = _
  rw [ht]
  exact LaxPointHom.left_action F _ _

lemma whiskerLeft_map (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    let : EnrichedOrdinaryCategory W C := ordinaryCategory F C t ht
    eHomWhiskerLeft W X g = F.map (eHomWhiskerLeft V X g) := by
  let : EnrichedOrdinaryCategory W C := ordinaryCategory F C t ht
  change (ρ_ (F.obj (X ⟶[V] Y))).inv ≫
    F.obj (X ⟶[V] Y) ◁ t (Y ⟶[V] Y') (eHomEquiv V g) ≫
      μ F _ _ ≫ F.map (eComp V X Y Y') = _
  rw [ht]
  exact LaxPointHom.right_action F _ _

def homFunctorIso :
    let : EnrichedOrdinaryCategory W C := ordinaryCategory F C t ht
    eHomFunctor V C ⋙ (CategoryTheory.Functor.whiskeringRight C V W).obj F ≅
      eHomFunctor W C := by
  let : EnrichedOrdinaryCategory W C := ordinaryCategory F C t ht
  refine NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun Y ↦ Iso.refl _) ?_) ?_
  · rename_i X
    intro Y Y' g
    change F.map (eHomWhiskerLeft V X.unop g) ≫ 𝟙 _ = 𝟙 _ ≫ eHomWhiskerLeft W X.unop g
    rw [whiskerLeft_map F C t ht, Category.id_comp, Category.comp_id]
  · intro X X' f
    apply NatTrans.ext
    funext Y
    change F.map (eHomWhiskerRight V f.unop Y) ≫ 𝟙 _ = 𝟙 _ ≫ eHomWhiskerRight W f.unop Y
    rw [whiskerRight_map F C t ht, Category.id_comp, Category.comp_id]

end SerrePositivity.TransportOrdinaryEnrichment
end

end TransportOrdinaryEnrichment
