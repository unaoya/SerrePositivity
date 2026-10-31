module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.TotalComplexSymmetry
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.LinearAlgebra.DirectSum.Finite
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.CategoryTheory.Monoidal.Linear
public import SerrePositivity.HomologicalAlgebra.FiniteSupportCoproduct
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.Algebra.Module.Projective

/-! # ℤ 添字 cochain 複体のテンソル積

## 概要

加群の ℤ 添字 cochain 複体のテンソル積 `cochainTensor`（全複体）と射のテンソル `cochainTensorMap` を作り、その加法性と係数環についての線形性、下限・上限、有界な複体の有限な次数、次数ごとの射影性を与える。

## 方針

Mathlib の `HomologicalComplex` のモノイダル構造（Algebra/Homology/Monoidal）の上に乗せる。

## 規約

`cochainTensor` は BS が名前で使うので残す。他の名前は Mathlib の記法（`⊗`・`⊗ₘ`・`α_` など）へ段階的に寄せる候補（refactor-plan §3.8 の 3、§4.3.2）。

## 使われ方

HomologicalAlgebra・PerfectComplex・KTheory/Adams のテンソル積の全体。
-/

@[expose] public noncomputable section

universe u

section CochainTensorPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Limits MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R]

/-- The standard total tensor complex, with the integer cochain sign convention. -/
abbrev cochainTensor (P Q : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ := HomologicalComplex.tensorObj P Q

/-- The inclusion of the summand of bidegree (i,j). -/
abbrev cochainTensorι (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (i j : ℤ) :
    P.X i ⊗ Q.X j ⟶ (cochainTensor P Q).X (i + j) :=
  ιTensorObj P Q i j (i + j) rfl

/-- Tensoring two chain maps gives a chain map. -/
abbrev cochainTensorMap {P Q P' Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') : cochainTensor P Q ⟶ cochainTensor P' Q' :=
  HomologicalComplex.tensorHom f g

/-- The associative comparison for the chosen total tensor complex. -/
abbrev cochainTensorAssociator (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) :
    cochainTensor (cochainTensor P Q) T ≅ cochainTensor P (cochainTensor Q T) :=
  HomologicalComplex.associator P Q T

/-- The differential on a homogeneous tensor has the standard Koszul sign. -/
lemma cochainTensorι_d (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (i j : ℤ) :
    cochainTensorι P Q i j ≫ (cochainTensor P Q).d (i + j) (i + j + 1) =
      (P.d i (i + 1) ▷ Q.X j) ≫
        ιTensorObj P Q (i + 1) j (i + j + 1) (by omega) +
      i.negOnePow • ((P.X i ◁ Q.d j (j + 1)) ≫
        ιTensorObj P Q i (j + 1) (i + j + 1) (by omega)) := by
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ rfl _ _ (by dsimp; omega),
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _ rfl _ (by dsimp; omega)]
  simp

/-- Each degree is the coproduct over bidegrees with the prescribed sum. -/
abbrev cochainTensorSummand (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n}) : ModuleCat.{u} R := P.X ij.val.1 ⊗ Q.X ij.val.2

/-- The chosen totalization and its categorical coproduct model agree. -/
def cochainTensorXIso (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (cochainTensor P Q).X n ≅ ∐ (cochainTensorSummand P Q n) := Iso.refl _

/-- The degree-zero unit complex for the chosen tensor. -/
abbrev cochainTensorUnit : CochainComplex (ModuleCat.{u} R) ℤ :=
  HomologicalComplex.tensorUnit (ModuleCat.{u} R) (.up ℤ)

/-- Left unit comparison. -/
abbrev cochainTensorLeftUnitor (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    cochainTensor cochainTensorUnit P ≅ P := HomologicalComplex.leftUnitor P

/-- Right unit comparison. -/
abbrev cochainTensorRightUnitor (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    cochainTensor P cochainTensorUnit ≅ P := HomologicalComplex.rightUnitor P
/-- Tensor maps act on homogeneous summands by ordinary tensor maps. -/
@[reassoc]
lemma ιTensorObj_cochainTensorMap {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') (i j n : ℤ) (h : i + j = n) :
    ιTensorObj P Q i j n h ≫ (cochainTensorMap f g).f n =
      (f.f i ⊗ₘ g.f j) ≫ ιTensorObj P' Q' i j n h := by
  rw [ι_mapBifunctorMap]
  change (f.f i ▷ Q.X j) ≫ (P'.X i ◁ g.f j) ≫ _ = _
  rw [tensorHom_def, Category.assoc]

@[reassoc]
lemma ιTensorObj_cochainTensor_d (A B : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j n : ℤ) (h : i + j = n) :
    ιTensorObj A B i j n h ≫ (cochainTensor A B).d n (n + 1) =
      (A.d i (i + 1) ▷ B.X j) ≫
        ιTensorObj A B (i + 1) j (n + 1) (by omega) +
      i.negOnePow • ((A.X i ◁ B.d j (j + 1)) ≫
        ιTensorObj A B i (j + 1) (n + 1) (by omega)) := by
  subst n
  exact cochainTensorι_d A B i j

end SerrePositivity

end CochainTensorPart

section CochainTensorLinearPart

set_option backward.isDefEq.respectTransparency false
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
lemma ι_whiskerLeft (P : CochainComplex (ModuleCat.{u} A) ℤ)
    {Q T : CochainComplex (ModuleCat.{u} A) ℤ} (f : Q ⟶ T)
    (i j n : ℤ) (h : i + j = n) :
    ιTensorObj P Q i j n h ≫ (P ◁ f).f n =
      (P.X i ◁ f.f j) ≫ ιTensorObj P T i j n h := by
  change ιTensorObj P Q i j n h ≫ (𝟙 P ⊗ₘ f).f n = _
  rw [ι_tensorHom]
  simp

/-- 右 tensor の双次数成分。 -/
@[reassoc (attr := simp)]
lemma ι_whiskerRight {Q T : CochainComplex (ModuleCat.{u} A) ℤ}
    (f : Q ⟶ T) (P : CochainComplex (ModuleCat.{u} A) ℤ)
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

namespace SerrePositivity
open CategoryTheory MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R]
variable {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}

lemma cochainTensorMap_smul_left {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (r : R) (f : P ⟶ P') (g : Q ⟶ Q') :
    cochainTensorMap (r • f) g = r • cochainTensorMap f g := by
  change (r • f) ⊗ₘ g = r • (f ⊗ₘ g)
  simp [tensorHom_def, Linear.smul_comp]

@[simp] lemma cochainTensorMap_zero_left {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (g : Q ⟶ Q') : cochainTensorMap (0 : P ⟶ P') g = 0 := by
  exact MonoidalPreadditive.zero_tensor g

lemma cochainTensorMap_add_left {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f f' : P ⟶ P') (g : Q ⟶ Q') :
    cochainTensorMap (f + f') g = cochainTensorMap f g + cochainTensorMap f' g := by
  exact MonoidalPreadditive.add_tensor f f' g

lemma cochainTensorMap_add_right {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ P') (g g' : Q ⟶ Q') :
    cochainTensorMap f (g + g') = cochainTensorMap f g + cochainTensorMap f g' := by
  exact MonoidalPreadditive.tensor_add f g g'

@[simp]
lemma cochainTensorMap_zero_zero : cochainTensorMap (0 : P ⟶ P') (0 : Q ⟶ Q') = 0 := by
  change (0 : P ⟶ P') ⊗ₘ (0 : Q ⟶ Q') = 0
  exact MonoidalPreadditive.tensor_zero (0 : P ⟶ P')

@[simp]
lemma cochainTensorMap_zero_right (f : P ⟶ P') : cochainTensorMap f (0 : Q ⟶ Q') = 0 := by
  exact MonoidalPreadditive.tensor_zero f

lemma cochainTensorMap_smul_right {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (r : R) (f : P ⟶ P') (g : Q ⟶ Q') :
    cochainTensorMap f (r • g) = r • cochainTensorMap f g := by
  change f ⊗ₘ (r • g) = r • (f ⊗ₘ g)
  simp [MonoidalCategory.tensorHom_def, Linear.comp_smul]

lemma cochainTensorMap_neg_left {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') : cochainTensorMap (-f) g = -cochainTensorMap f g := by
  simpa using cochainTensorMap_smul_left (-1 : R) f g

lemma cochainTensorMap_neg_right {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') : cochainTensorMap f (-g) = -cochainTensorMap f g := by
  simpa using cochainTensorMap_smul_right (-1 : R) f g

lemma cochainTensorMap_sub_left {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f f' : P ⟶ P') (g : Q ⟶ Q') :
    cochainTensorMap (f - f') g = cochainTensorMap f g - cochainTensorMap f' g := by
  simp only [sub_eq_add_neg, cochainTensorMap_add_left, cochainTensorMap_neg_left]

lemma cochainTensorMap_sub_right {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ P') (g g' : Q ⟶ Q') :
    cochainTensorMap f (g - g') = cochainTensorMap f g - cochainTensorMap f g' := by
  simp only [sub_eq_add_neg, cochainTensorMap_add_right, cochainTensorMap_neg_right]

lemma cochainTensorMap_sum_left {J : Type*}
    {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (s : Finset J) (f : J → (P ⟶ P')) (g : Q ⟶ Q') :
    cochainTensorMap (∑ j ∈ s, f j) g = ∑ j ∈ s, cochainTensorMap (f j) g :=
  CategoryTheory.sum_tensor s g f

lemma cochainTensorMap_sum_right {J : Type*}
    {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (s : Finset J) (f : P ⟶ P') (g : J → (Q ⟶ Q')) :
    cochainTensorMap f (∑ j ∈ s, g j) = ∑ j ∈ s, cochainTensorMap f (g j) :=
  CategoryTheory.tensor_sum s f g

end SerrePositivity

end CochainTensorLinearPart

section CochainTensorProjectivePart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Limits MonoidalCategory
variable {R : Type u} [CommRing R]

/-- Projectivity of the factors implies projectivity of every total tensor degree. -/
lemma cochainTensor_projective_X (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : ∀ i, Module.Projective R (P.X i)) (hq : ∀ j, Module.Projective R (Q.X j)) (n : ℤ) :
    Module.Projective R ((cochainTensor P Q).X n) := by
  have hs : ∀ ij, Projective (cochainTensorSummand P Q n ij) := by
    intro ij
    have := hp ij.val.1
    have := hq ij.val.2
    have ht : Module.Projective R (TensorProduct R (P.X ij.val.1) (Q.X ij.val.2)) :=
      inferInstance
    exact ModuleCat.projective_of_categoryTheory_projective _
  have : Projective ((cochainTensor P Q).X n) :=
    Projective.of_iso (cochainTensorXIso P Q n).symm
      (projective_coproduct_of_projective _ hs)
  infer_instance

end SerrePositivity

end CochainTensorProjectivePart
