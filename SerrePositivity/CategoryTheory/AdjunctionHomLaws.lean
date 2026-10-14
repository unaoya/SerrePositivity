module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.HomCongr

/-! # 随伴の転置・逆転置の法則の命題としての公開 -/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace SerrePositivity.AdjunctionHomLaws

open CategoryTheory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)

/-- 転置して逆転置すると元の射になるという法則。 -/
def uncurryCurryLaw {X : C} {Y : D} (f : L.obj X ⟶ Y) : Prop :=
  (a.homEquiv X Y).symm (a.homEquiv X Y f) = f

/-- 逆転置して転置すると元の射になるという法則。 -/
def curryUncurryLaw {X : C} {Y : D} (f : X ⟶ R.obj Y) : Prop :=
  a.homEquiv X Y ((a.homEquiv X Y).symm f) = f

/-- 転置の値域の射に関する自然性の法則。 -/
def curryNaturalityRightLaw {X : C} {Y Z : D} (f : L.obj X ⟶ Y) (g : Y ⟶ Z) : Prop :=
  a.homEquiv X Z (f ≫ g) = a.homEquiv X Y f ≫ R.map g

/-- 転置のパラメータの射に関する自然性の法則。 -/
def curryNaturalityLeftLaw {X Y : C} {Z : D} (f : X ⟶ Y) (g : L.obj Y ⟶ Z) : Prop :=
  a.homEquiv X Z (L.map f ≫ g) = f ≫ a.homEquiv Y Z g

/-- 随伴の転置のパラメータに関する自然性。 -/
lemma curry_naturality_left {X Y : C} {Z : D} (f : X ⟶ Y) (g : L.obj Y ⟶ Z) :
    curryNaturalityLeftLaw a f g := a.homEquiv_naturality_left f g

/-- 随伴の転置・逆転置の左相互逆性。 -/
lemma uncurry_curry {X : C} {Y : D} (f : L.obj X ⟶ Y) : uncurryCurryLaw a f :=
  (a.homEquiv X Y).left_inv f

/-- 随伴の転置・逆転置の右相互逆性。 -/
lemma curry_uncurry {X : C} {Y : D} (f : X ⟶ R.obj Y) : curryUncurryLaw a f :=
  (a.homEquiv X Y).right_inv f

/-- 随伴の転置の値域に関する自然性。 -/
lemma curry_naturality_right {X : C} {Y Z : D} (f : L.obj X ⟶ Y) (g : Y ⟶ Z) :
    curryNaturalityRightLaw a f g := a.homEquiv_naturality_right f g

/-- 転置した射を左随伴で送って評価すると元の射になるという法則。 -/
def curryEvaluationLaw {X : C} {Y : D} (f : L.obj X ⟶ Y) : Prop :=
  L.map (a.homEquiv X Y f) ≫ a.counit.app Y = f

/-- 転置した射を評価すると元の射になる。 -/
lemma curry_evaluation {X : C} {Y : D} (f : L.obj X ⟶ Y) :
    curryEvaluationLaw a f := by
  change L.map (a.homEquiv X Y f) ≫ a.counit.app Y = f
  exact (a.homEquiv X Y).left_inv f

/-- 左随伴で送って評価した二つの射が等しいという法則。 -/
def evaluationEqualityLaw {X : C} {Y : D} (f g : X ⟶ R.obj Y) : Prop :=
  L.map f ≫ a.counit.app Y = L.map g ≫ a.counit.app Y

/-- 右随伴への射は左随伴で送った後の評価で決まる。 -/
lemma evaluation_injective {X : C} {Y : D} (f g : X ⟶ R.obj Y)
    (h : evaluationEqualityLaw a f g) : f = g :=
  (a.homEquiv X Y).symm.injective h

/-- 転置した射への前合成を、評価後の等式から特徴付ける法則。 -/
def curryPreEqualityLaw {X Z : C} {Y : D} (f : L.obj X ⟶ Y)
    (t : Z ⟶ X) (s : Z ⟶ R.obj Y) : Prop :=
  t ≫ a.homEquiv X Y f = s

/-- 前合成した転置は評価後の等式で決まる。 -/
lemma curry_pre_eq_of_evaluation {X Z : C} {Y : D} (f : L.obj X ⟶ Y)
    (t : Z ⟶ X) (s : Z ⟶ R.obj Y)
    (h : L.map t ≫ f = L.map s ≫ a.counit.app Y) : curryPreEqualityLaw a f t s := by
  apply evaluation_injective a
  change L.map (t ≫ a.homEquiv X Y f) ≫ a.counit.app Y = _
  rw [L.map_comp, Category.assoc]
  have hc := curry_evaluation a f
  change L.map (a.homEquiv X Y f) ≫ a.counit.app Y = f at hc
  rw [hc]
  exact h

/-- 左随伴の指定した対象との比較から、元の射を右随伴への射へ転置する同値。 -/
def comparisonHomEquiv {I : C} {E : D} (e : L.obj I ≅ E) (F : D) :
    (E ⟶ F) ≃ (I ⟶ R.obj F) :=
  (Iso.homCongr e.symm (Iso.refl F)).trans (a.homEquiv I F)

/-- 比較を使うHom同値の順写像。 -/
lemma comparisonHomEquiv_apply {I : C} {E F : D} (e : L.obj I ≅ E) (f : E ⟶ F) :
    comparisonHomEquiv a e F f = a.homEquiv I F (e.hom ≫ f) := by
  simp only [comparisonHomEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.symm_inv, Iso.refl_hom, Category.comp_id]

/-- 比較を使うHom同値の逆写像。 -/
lemma comparisonHomEquiv_symm_apply {I : C} {E F : D} (e : L.obj I ≅ E)
    (f : I ⟶ R.obj F) :
    (comparisonHomEquiv a e F).symm f = e.inv ≫ (a.homEquiv I F).symm f := by
  change e.inv ≫ ((a.homEquiv I F).symm f ≫ 𝟙 F) = _
  rw [Category.comp_id]

/-- 恒等射を比較の順射の転置へ送るという法則。 -/
def comparisonHomIdentityLaw {I : C} {E : D} (e : L.obj I ≅ E) : Prop :=
  comparisonHomEquiv a e E (𝟙 E) = a.homEquiv I E e.hom

/-- 恒等射は比較の順射を転置した射に対応する。 -/
lemma comparisonHomEquiv_id {I : C} {E : D} (e : L.obj I ≅ E) :
    comparisonHomIdentityLaw a e := by
  unfold comparisonHomIdentityLaw
  rw [comparisonHomEquiv_apply, Category.comp_id]

end SerrePositivity.AdjunctionHomLaws
