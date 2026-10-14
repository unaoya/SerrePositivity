module

public import SerrePositivity.CategoryTheory.AdjunctionHomLaws
public import Mathlib.CategoryTheory.Monoidal.Category

/-! # 作用の表現性から得る写像対象の左単位の評価 -/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace SerrePositivity.MappingUnitLaws

open CategoryTheory CategoryTheory.MonoidalCategory

variable {V : Type u₁} {D : Type u₂} [Category.{v₁} V] [Category.{v₂} D]
  [MonoidalCategory V] (H : V ⥤ D ⥤ D)

/-- 作用の値域を固定したパラメータ関手。 -/
abbrev parameterFunctor (E : D) : V ⥤ D where
  obj X := (H.obj X).obj E
  map f := (H.map f).app E
  map_id X := by rw [H.map_id]; rfl
  map_comp f g := by rw [H.map_comp]; rfl

variable (u : H.obj (𝟙_ V) ≅ 𝟭 D)

/-- 写像対象の左単位の評価を、作用の単位と結同比較から計算する。 -/
lemma left_unit_evaluation {P Q : V} {E F : D} (h : 𝟙_ V ⟶ P)
    (v : (H.obj Q).obj E ⟶ F) (w : (H.obj P).obj F ⟶ F)
    (b : (parameterFunctor H E).obj (P ⊗ Q) ⟶ (H.obj P).obj ((H.obj Q).obj E))
    (b₀ : (parameterFunctor H E).obj ((𝟙_ V) ⊗ Q) ⟶ (H.obj (𝟙_ V)).obj ((H.obj Q).obj E))
    (hb : (parameterFunctor H E).map (h ⊗ₘ 𝟙 Q) ≫ b = b₀ ≫ (H.map h).app ((H.obj Q).obj E))
    (hw : (H.map h).app F ≫ w = u.hom.app F)
    (hu : b₀ ≫ u.hom.app ((H.obj Q).obj E) = (parameterFunctor H E).map (λ_ Q).hom) :
    (parameterFunctor H E).map (h ⊗ₘ 𝟙 Q) ≫ b ≫ (H.obj P).map v ≫ w =
      (parameterFunctor H E).map (λ_ Q).hom ≫ v := by
  erw [← Category.assoc, ← Category.assoc, hb]
  simp only [Category.assoc]
  erw [← reassoc_of% ((H.map h).naturality v)]
  erw [hw, u.hom.naturality v, ← Category.assoc, hu]
  rfl

/-- 写像対象の右単位の評価を、作用の単位と結同比較から計算する。 -/
lemma right_unit_evaluation {P Q : V} {E F : D} (h : 𝟙_ V ⟶ Q)
    (v : (H.obj P).obj E ⟶ F) (w : (H.obj Q).obj E ⟶ E)
    (b : (parameterFunctor H E).obj (P ⊗ Q) ⟶ (H.obj P).obj ((H.obj Q).obj E))
    (b₀ : (parameterFunctor H E).obj (P ⊗ (𝟙_ V)) ⟶
      (H.obj P).obj ((H.obj (𝟙_ V)).obj E))
    (hb : (parameterFunctor H E).map (𝟙 P ⊗ₘ h) ≫ b =
      b₀ ≫ (H.obj P).map ((H.map h).app E))
    (hw : (H.map h).app E ≫ w = u.hom.app E)
    (hu : b₀ ≫ (H.obj P).map (u.hom.app E) = (parameterFunctor H E).map (ρ_ P).hom) :
    (parameterFunctor H E).map (𝟙 P ⊗ₘ h) ≫ b ≫ (H.obj P).map w ≫ v =
      (parameterFunctor H E).map (ρ_ P).hom ≫ v := by
  erw [← Category.assoc, ← Category.assoc, hb]
  simp only [Category.assoc]
  erw [← CategoryTheory.Functor.map_comp_assoc, hw, ← Category.assoc, hu]

end SerrePositivity.MappingUnitLaws
