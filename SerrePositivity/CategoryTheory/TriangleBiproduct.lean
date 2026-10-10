module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-! # 二つの完全三角形の直和 -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Preadditive

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

noncomputable section

@[reassoc]
lemma biprodDescComp {X Y Z W : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ W) :
    biprod.desc f g ≫ h = biprod.desc (f ≫ h) (g ≫ h) := by
  apply biprod.hom_ext' <;> simp

/-- 三頂点に二項直和を使った三角形。 -/
@[simps!]
def triangleBiproduct (T U : Triangle C) : Triangle C :=
  Triangle.mk (biprod.map T.mor₁ U.mor₁) (biprod.map T.mor₂ U.mor₂)
    (biprod.desc (T.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map biprod.inl)
      (U.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map biprod.inr))

@[simps]
def triangleBiproductFst (T U : Triangle C) : triangleBiproduct T U ⟶ T where
  hom₁ := biprod.fst
  hom₂ := biprod.fst
  hom₃ := biprod.fst
  comm₁ := by simp [triangleBiproduct]
  comm₂ := by simp [triangleBiproduct]
  comm₃ := by
    dsimp [triangleBiproduct]
    apply biprod.hom_ext'
    all_goals simp [← CategoryTheory.Functor.map_comp]

@[simps]
def triangleBiproductSnd (T U : Triangle C) : triangleBiproduct T U ⟶ U where
  hom₁ := biprod.snd
  hom₂ := biprod.snd
  hom₃ := biprod.snd
  comm₁ := by simp [triangleBiproduct]
  comm₂ := by simp [triangleBiproduct]
  comm₃ := by
    dsimp [triangleBiproduct]
    apply biprod.hom_ext'
    all_goals simp [← CategoryTheory.Functor.map_comp]

/-- 二項直和から Bool で添字づけた積への標準射は同型。 -/
lemma isIso_biprod_to_bool_product (X : Bool → C) :
    IsIso (Pi.lift (fun b : Bool ↦ Bool.rec
      (biprod.fst : X false ⊞ X true ⟶ X false) biprod.snd b)) := by
  let f := Pi.lift (fun b : Bool ↦ Bool.rec
    (biprod.fst : X false ⊞ X true ⟶ X false) biprod.snd b)
  refine ⟨⟨biprod.lift (Pi.π X false) (Pi.π X true), ?_, ?_⟩⟩
  · apply biprod.hom_ext
    all_goals simp
  · apply Pi.hom_ext
    intro b
    cases b <;> simp

lemma triangleBiproduct_distinguished (T U : Triangle C)
    (hT : T ∈ distTriang C) (hU : U ∈ distTriang C) :
    triangleBiproduct T U ∈ distTriang C := by
  let V : Bool → Triangle C := Bool.rec T U
  let f := productTriangle.lift V (Bool.rec (triangleBiproductFst T U)
    (triangleBiproductSnd T U))
  have h₁ : IsIso f.hom₁ := by
    have he : f.hom₁ = Pi.lift (f := fun b ↦ (V b).obj₁) (fun b : Bool ↦ Bool.rec
        (motive := fun b ↦ T.obj₁ ⊞ U.obj₁ ⟶ (V b).obj₁) biprod.fst biprod.snd b) := by
      apply Pi.hom_ext
      intro b
      cases b <;> simp [f]
    rw [he]
    exact isIso_biprod_to_bool_product (fun b ↦ (V b).obj₁)
  have h₂ : IsIso f.hom₂ := by
    have he : f.hom₂ = Pi.lift (f := fun b ↦ (V b).obj₂) (fun b : Bool ↦ Bool.rec
        (motive := fun b ↦ T.obj₂ ⊞ U.obj₂ ⟶ (V b).obj₂) biprod.fst biprod.snd b) := by
      apply Pi.hom_ext
      intro b
      cases b <;> simp [f]
    rw [he]
    exact isIso_biprod_to_bool_product (fun b ↦ (V b).obj₂)
  have h₃ : IsIso f.hom₃ := by
    have he : f.hom₃ = Pi.lift (f := fun b ↦ (V b).obj₃) (fun b : Bool ↦ Bool.rec
        (motive := fun b ↦ T.obj₃ ⊞ U.obj₃ ⟶ (V b).obj₃) biprod.fst biprod.snd b) := by
      apply Pi.hom_ext
      intro b
      cases b <;> simp [f]
    rw [he]
    exact isIso_biprod_to_bool_product (fun b ↦ (V b).obj₃)
  have : IsIso f := Triangle.isIso_of_isIsos f h₁ h₂ h₃
  exact isomorphic_distinguished _ (productTriangle_distinguished V
    (by intro b; cases b <;> assumption)) _ (asIso f)

end

end SerrePositivity
