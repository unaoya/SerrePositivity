module
public import Mathlib.Algebra.Homology.Linear
public import SerrePositivity.HomologicalAlgebra.CochainTensor
public import Mathlib.CategoryTheory.Monoidal.Linear

/-! # Ch(A) の tensor の加法性と A 線形性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex
variable {A : Type u} [CommRing A]

/-- 非有界 tensor の射の等式を双次数成分へ帰着する。 -/
lemma tensorHom_ext {P Q T : CochainComplex (ModuleCat.{u} A) ℤ} {f g : P ⊗ Q ⟶ T}
    (h : ∀ i j n (hn : i + j = n),
      ιTensorObj P Q i j n hn ≫ f.f n = ιTensorObj P Q i j n hn ≫ g.f n) : f = g := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact mapBifunctor.hom_ext (fun i j hn => h i j n hn)

/-- tensor 射の双次数成分。 -/
@[reassoc (attr := simp)]
lemma ι_tensorHom {P Q P' Q' : CochainComplex (ModuleCat.{u} A) ℤ} (f : P ⟶ P') (g : Q ⟶ Q')
    (i j n : ℤ) (h : i + j = n) :
    ιTensorObj P Q i j n h ≫ (f ⊗ₘ g).f n =
      (f.f i ⊗ₘ g.f j) ≫ ιTensorObj P' Q' i j n h :=
  SerrePositivity.ιTensorObj_cochainTensorMap f g i j n h

/-- 左 tensor の双次数成分。 -/
@[reassoc (attr := simp)]
lemma ι_whiskerLeft (P : CochainComplex (ModuleCat.{u} A) ℤ) {Q T : CochainComplex (ModuleCat.{u} A) ℤ} (f : Q ⟶ T)
    (i j n : ℤ) (h : i + j = n) :
    ιTensorObj P Q i j n h ≫ (P ◁ f).f n =
      (P.X i ◁ f.f j) ≫ ιTensorObj P T i j n h := by
  change ιTensorObj P Q i j n h ≫ (𝟙 P ⊗ₘ f).f n = _
  rw [ι_tensorHom]
  simp

/-- 右 tensor の双次数成分。 -/
@[reassoc (attr := simp)]
lemma ι_whiskerRight {Q T : CochainComplex (ModuleCat.{u} A) ℤ} (f : Q ⟶ T) (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (i j n : ℤ) (h : i + j = n) :
    ιTensorObj Q P i j n h ≫ (f ▷ P).f n =
      (f.f i ▷ P.X j) ≫ ιTensorObj T P i j n h := by
  change ιTensorObj Q P i j n h ≫ (f ⊗ₘ 𝟙 P).f n = _
  rw [ι_tensorHom]
  simp

/-- Ch(A) の tensor は両変数で加法的。直和成分上の加法性を用いる。 -/
instance complexMonoidalPreadditive : MonoidalPreadditive (CochainComplex (ModuleCat.{u} A) ℤ) where
  whiskerLeft_zero := by
    intro P Q T
    apply tensorHom_ext
    intro i j n hn
    rw [ι_whiskerLeft]
    simp
  zero_whiskerRight := by
    intro P Q T
    apply tensorHom_ext
    intro i j n hn
    rw [ι_whiskerRight]
    simp
  whiskerLeft_add := by
    intro P Q T f g
    apply tensorHom_ext
    intro i j n hn
    rw [ι_whiskerLeft]
    simp [Preadditive.comp_add, Preadditive.add_comp]
  add_whiskerRight := by
    intro P Q T f g
    apply tensorHom_ext
    intro i j n hn
    rw [ι_whiskerRight]
    simp [Preadditive.comp_add, Preadditive.add_comp]

/-- Ch(A) の tensor は両変数で A 線形。 -/
instance complexMonoidalLinear : MonoidalLinear A (CochainComplex (ModuleCat.{u} A) ℤ) where
  whiskerLeft_smul := by
    intro P Q T a f
    apply tensorHom_ext
    intro i j n hn
    rw [ι_whiskerLeft]
    simp [Linear.smul_comp, Linear.comp_smul]
  smul_whiskerRight := by
    intro a Q T f P
    apply tensorHom_ext
    intro i j n hn
    rw [ι_whiskerRight]
    simp [Linear.smul_comp, Linear.comp_smul]
end SerrePositivity.DifferentialGraded
