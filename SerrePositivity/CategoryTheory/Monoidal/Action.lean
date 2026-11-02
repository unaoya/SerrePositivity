module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Whiskering

/-!
# Monoidal.Action

## 概要
関連する圏論の構成と補題をまとめる。各構成の詳細は以下の元モジュールの説明を参照。

## 方針
元の宣言と証明を保持し、依存順に section を分けて配置する。

## 規約
公開宣言名・名前空間・宇宙変数の意味を変更しない。元の module docstring は各節に保存する。

## 使われ方
旧モジュールの利用元は `SerrePositivity.CategoryTheory.Monoidal.Action` を直接 import する。
-/

/-! ## ActionProductComparison（旧 SerrePositivity/CategoryTheory/Monoidal/ActionProductComparison.lean） -/

/-! # パラメータの積の比較を作用の反復比較へ送る -/

@[expose] public section ActionProductComparison
universe v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

namespace SerrePositivity.ActionProductComparison

open CategoryTheory CategoryTheory.MonoidalCategory

variable {W : Type u₁} {V : Type u₂} {C : Type u₃}
  [Category.{v₁} W] [Category.{v₂} V] [Category.{v₃} C]
  [MonoidalCategory W] [MonoidalCategory V]
  (P : W ⥤ V) (H : V ⥤ C ⥤ C)
  (a : ∀ X Y, H.obj (X ⊗ Y) ≅ H.obj Y ⋙ H.obj X)
  (m : ∀ K L, P.obj K ⊗ P.obj L ≅ P.obj (K ⊗ L))

/-- パラメータの積を作用の結同比較に接続した自然同型。 -/
def productNatIso (K L : W) : H.obj (P.obj (K ⊗ L)) ≅ H.obj (P.obj L) ⋙ H.obj (P.obj K) :=
  H.mapIso (m K L).symm ≪≫ a (P.obj K) (P.obj L)

/-- 反復比較のパラメータの両変数の自然性の等式。 -/
def parameterLaw {K K' L L' : W} (f : K ⟶ K') (g : L ⟶ L') (E : C) : Prop :=
  (H.map (P.map (f ⊗ₘ g))).app E ≫ (productNatIso P H a m K' L').hom.app E =
    (productNatIso P H a m K L).hom.app E ≫
      (H.map (P.map f)).app ((H.obj (P.obj L)).obj E) ≫
        (H.obj (P.obj K')).map ((H.map (P.map g)).app E)

/-- 積の比較と作用の結同比較の自然性から、反復比較の両変数の自然性を得る。 -/
lemma parameter {K K' L L' : W} (f : K ⟶ K') (g : L ⟶ L') (E : C)
    (hm : P.map (f ⊗ₘ g) ≫ (m K' L').inv =
      (m K L).inv ≫ (P.map f ⊗ₘ P.map g))
    (ha : (H.map (P.map f ⊗ₘ P.map g)).app E ≫ (a (P.obj K') (P.obj L')).hom.app E =
      (a (P.obj K) (P.obj L)).hom.app E ≫
        (H.map (P.map f)).app ((H.obj (P.obj L)).obj E) ≫
          (H.obj (P.obj K')).map ((H.map (P.map g)).app E)) :
    parameterLaw P H a m f g E := by
  unfold parameterLaw productNatIso
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [← Category.assoc, ← NatTrans.comp_app, ← H.map_comp, hm, H.map_comp,
    NatTrans.comp_app, Category.assoc, ha]
  simp only [Category.assoc]

end SerrePositivity.ActionProductComparison
end

end ActionProductComparison

/-! ## TensorActionTransport（旧 SerrePositivity/CategoryTheory/Monoidal/TensorActionTransport.lean） -/

/-! # テンソル作用の自然比較による結同比較の移送 -/

@[expose] public section TensorActionTransport
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

/-- 第二パラメータを固定した結同比較の自然性の法則。 -/
def associatorParameterLeftLaw {X X' : V} (f : X ⟶ X') (Y : V) (A : C) : Prop :=
  (H.map (f ⊗ₘ 𝟙 Y)).app A ≫ (associatorNatIso F H e μ X' Y).hom.app A =
    (associatorNatIso F H e μ X Y).hom.app A ≫ (H.map f).app ((H.obj Y).obj A)

/-- 第二パラメータの恒等射を除いた結同比較の自然性。 -/
lemma associator_parameter_left {X X' : V} (f : X ⟶ X') (Y : V) (A : C)
    (hμ : (F.map f ⊗ₘ F.map (𝟙 Y)) ≫ (μ X' Y).hom =
      (μ X Y).hom ≫ F.map (f ⊗ₘ 𝟙 Y)) :
    associatorParameterLeftLaw F H e μ f Y A := by
  have h := associator_parameter_naturality_of_hom F H e μ f (𝟙 Y) A hμ
  unfold associatorParameterLaw at h
  rw [H.map_id] at h
  change (H.map (f ⊗ₘ 𝟙 Y)).app A ≫ (associatorNatIso F H e μ X' Y).hom.app A =
    (associatorNatIso F H e μ X Y).hom.app A ≫
      (H.map f).app ((H.obj Y).obj A) ≫ (H.obj X').map (𝟙 ((H.obj Y).obj A)) at h
  rw [CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact h

/-- 第一パラメータを固定した結同比較の自然性の法則。 -/
def associatorParameterRightLaw (X : V) {Y Y' : V} (g : Y ⟶ Y') (A : C) : Prop :=
  (H.map (𝟙 X ⊗ₘ g)).app A ≫ (associatorNatIso F H e μ X Y').hom.app A =
    (associatorNatIso F H e μ X Y).hom.app A ≫ (H.obj X).map ((H.map g).app A)

/-- 第一パラメータの恒等射を除いた結同比較の自然性。 -/
lemma associator_parameter_right (X : V) {Y Y' : V} (g : Y ⟶ Y') (A : C)
    (hμ : (F.map (𝟙 X) ⊗ₘ F.map g) ≫ (μ X Y').hom =
      (μ X Y).hom ≫ F.map (𝟙 X ⊗ₘ g)) :
    associatorParameterRightLaw F H e μ X g A := by
  have h := associator_parameter_naturality_of_hom F H e μ (𝟙 X) g A hμ
  unfold associatorParameterLaw at h
  rw [H.map_id] at h
  change (H.map (𝟙 X ⊗ₘ g)).app A ≫ (associatorNatIso F H e μ X Y').hom.app A =
    (associatorNatIso F H e μ X Y).hom.app A ≫
      𝟙 ((H.obj X).obj ((H.obj Y).obj A)) ≫ (H.obj X).map ((H.map g).app A) at h
  erw [Category.id_comp] at h
  exact h

end SerrePositivity.TensorActionTransport
end

end TensorActionTransport
