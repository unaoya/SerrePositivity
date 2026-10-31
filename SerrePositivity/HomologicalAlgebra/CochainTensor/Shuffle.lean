module

public import SerrePositivity.HomologicalAlgebra.CochainTensor.Symmetric

/-! # テンソル積の入れ替えとコヒーレンス

## 概要

四つ・六つのテンソル因子のシャッフル、三因子の符号付き回転、同次元の公式、二因子・三因子の微分、選んだ同次和因子のスカラー座標を与え、符号付き対称性の六角形の両立と、それが与える対称モノイダル構造を示す。シャッフルがブロックの交換と対角の交換（六因子では巡回と対角の回転）を絡めることも示す。

## 方針

同次元の公式で各和因子の上の値を計算し、等式を和因子ごとに確かめる。

## 規約

`cochainTensorShuffle` は Mathlib の `MonoidalCategory.tensorμ` と同じ（確度高、refactor-plan §4.3.2）。四因子と六因子の API は項数違いの同じもの（一般化は記録のみ）。

## 使われ方

PerfectComplex のテンソルの巡回和・固有分解、KTheory/Adams。
-/

@[expose] public noncomputable section

universe u

section CochainTensorShufflePart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R]

@[reassoc]
lemma ιTensorObj_cochainTensorAssociator_hom
    (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) (i j k n : ℤ) (h : i + j + k = n) :
    (ιTensorObj P Q i j (i + j) rfl ▷ T.X k) ≫
      ιTensorObj (cochainTensor P Q) T (i + j) k n h ≫
      (cochainTensorAssociator P Q T).hom.f n =
    (α_ (P.X i) (Q.X j) (T.X k)).hom ≫
      (P.X i ◁ ιTensorObj Q T j k (j + k) rfl) ≫
      ιTensorObj P (cochainTensor Q T) i (j + k) n (by omega) :=
  GradedObject.Monoidal.ιTensorObj₃'_associator_hom P.X Q.X T.X i j k n h

@[reassoc]
lemma ιTensorObj_cochainTensorAssociator_inv
    (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) (i j k n : ℤ) (h : i + j + k = n) :
    (P.X i ◁ ιTensorObj Q T j k (j + k) rfl) ≫
      ιTensorObj P (cochainTensor Q T) i (j + k) n (by omega) ≫
      (cochainTensorAssociator P Q T).inv.f n =
    (α_ (P.X i) (Q.X j) (T.X k)).inv ≫
      (ιTensorObj P Q i j (i + j) rfl ▷ T.X k) ≫
      ιTensorObj (cochainTensor P Q) T (i + j) k n h :=
  GradedObject.Monoidal.ιTensorObj₃_associator_inv P.X Q.X T.X i j k n h

def cochainTensorIso {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (e : P ≅ P') (f : Q ≅ Q') : cochainTensor P Q ≅ cochainTensor P' Q' :=
  MonoidalCategory.tensorIso e f

/-- Move the two middle factors past each other, with the existing Koszul-signed symmetry. -/
def cochainTensorShuffle (P Q T U : CochainComplex (ModuleCat.{u} R) ℤ) :
    cochainTensor (cochainTensor P Q) (cochainTensor T U) ≅
      cochainTensor (cochainTensor P T) (cochainTensor Q U) :=
  cochainTensorAssociator P Q (cochainTensor T U) ≪≫
    cochainTensorIso (Iso.refl P) (cochainTensorAssociator Q T U).symm ≪≫
    cochainTensorIso (Iso.refl P)
      (cochainTensorIso (cochainTensorSymmetry Q T) (Iso.refl U)) ≪≫
    cochainTensorIso (Iso.refl P) (cochainTensorAssociator T Q U) ≪≫
    (cochainTensorAssociator P T (cochainTensor Q U)).symm

end SerrePositivity

end CochainTensorShufflePart

section CochainTensorHomogeneousPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
open scoped TensorProduct
variable {R : Type u} [CommRing R]

lemma cochainTensorX_whiskerRight_hom_ext
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) (T Y : ModuleCat.{u} R)
    {f g : (cochainTensor P Q).X n ⊗ T ⟶ Y}
    (h : ∀ i j (hij : i + j = n), (ιTensorObj P Q i j n hij ▷ T) ≫ f =
      (ιTensorObj P Q i j n hij ▷ T) ≫ g) : f = g := by
  apply (isColimitOfHasCoproductOfPreservesColimit
    (tensorRight T) (cochainTensorSummand P Q n)).hom_ext
  intro ij
  exact h ij.as.val.1 ij.as.val.2 ij.as.property

lemma cochainTensorX_whiskerLeft_hom_ext
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) (T Y : ModuleCat.{u} R)
    {f g : T ⊗ (cochainTensor P Q).X n ⟶ Y}
    (h : ∀ i j (hij : i + j = n), (T ◁ ιTensorObj P Q i j n hij) ≫ f =
      (T ◁ ιTensorObj P Q i j n hij) ≫ g) : f = g := by
  apply (isColimitOfHasCoproductOfPreservesColimit
    (tensorLeft T) (cochainTensorSummand P Q n)).hom_ext
  intro ij
  exact h ij.as.val.1 ij.as.val.2 ij.as.property

lemma cochainTensorAssociator_hom_apply_ι
    (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) (i j k n : ℤ) (h : i + j + k = n)
    (x : P.X i) (y : Q.X j) (z : T.X k) :
    (cochainTensorAssociator P Q T).hom.f n
      (ιTensorObj (cochainTensor P Q) T (i + j) k n h
        ((ιTensorObj P Q i j (i + j) rfl) (x ⊗ₜ[R] y) ⊗ₜ[R] z)) =
    ιTensorObj P (cochainTensor Q T) i (j + k) n (by omega)
      (x ⊗ₜ[R] (ιTensorObj Q T j k (j + k) rfl) (y ⊗ₜ[R] z)) :=
  congrArg (fun f => f ((x ⊗ₜ[R] y) ⊗ₜ[R] z))
    (ιTensorObj_cochainTensorAssociator_hom P Q T i j k n h)

lemma cochainTensorAssociator_inv_apply_ι
    (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) (i j k n : ℤ) (h : i + j + k = n)
    (x : P.X i) (y : Q.X j) (z : T.X k) :
    (cochainTensorAssociator P Q T).inv.f n
      (ιTensorObj P (cochainTensor Q T) i (j + k) n (by omega)
        (x ⊗ₜ[R] (ιTensorObj Q T j k (j + k) rfl) (y ⊗ₜ[R] z))) =
    ιTensorObj (cochainTensor P Q) T (i + j) k n h
      ((ιTensorObj P Q i j (i + j) rfl) (x ⊗ₜ[R] y) ⊗ₜ[R] z) :=
  congrArg (fun f => f (x ⊗ₜ[R] (y ⊗ₜ[R] z)))
    (ιTensorObj_cochainTensorAssociator_inv P Q T i j k n h)

lemma cochainTensorAssociator_hom_apply_ι_of_sum
    (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) (i j k s n : ℤ)
    (hs : i + j = s) (h : s + k = n) (x : P.X i) (y : Q.X j) (z : T.X k) :
    (cochainTensorAssociator P Q T).hom.f n
      (ιTensorObj (cochainTensor P Q) T s k n h
        ((ιTensorObj P Q i j s hs) (x ⊗ₜ[R] y) ⊗ₜ[R] z)) =
    ιTensorObj P (cochainTensor Q T) i (j + k) n (by omega)
      (x ⊗ₜ[R] (ιTensorObj Q T j k (j + k) rfl) (y ⊗ₜ[R] z)) := by
  subst s
  exact cochainTensorAssociator_hom_apply_ι P Q T i j k n h x y z

lemma cochainTensorAssociator_inv_apply_ι_of_sum
    (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) (i j k s n : ℤ)
    (hs : j + k = s) (h : i + s = n) (x : P.X i) (y : Q.X j) (z : T.X k) :
    (cochainTensorAssociator P Q T).inv.f n
      (ιTensorObj P (cochainTensor Q T) i s n h
        (x ⊗ₜ[R] (ιTensorObj Q T j k s hs) (y ⊗ₜ[R] z))) =
    ιTensorObj (cochainTensor P Q) T (i + j) k n (by omega)
      ((ιTensorObj P Q i j (i + j) rfl) (x ⊗ₜ[R] y) ⊗ₜ[R] z) := by
  subst s
  exact cochainTensorAssociator_inv_apply_ι P Q T i j k n (by omega) x y z

lemma cochainTensor_d_apply_ι (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j n : ℤ) (h : i + j = n) (x : P.X i) (y : Q.X j) :
    (cochainTensor P Q).d n (n + 1) (ιTensorObj P Q i j n h (x ⊗ₜ[R] y)) =
      ιTensorObj P Q (i + 1) j (n + 1) (by omega) (P.d i (i + 1) x ⊗ₜ[R] y) +
      i.negOnePow • ιTensorObj P Q i (j + 1) (n + 1) (by omega) (x ⊗ₜ[R] Q.d j (j + 1) y) := by
  have he := congrArg (fun f => f (x ⊗ₜ[R] y)) (ιTensorObj_cochainTensor_d P Q i j n h)
  exact he

lemma cochainTensorMap_apply_ι {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') (i j n : ℤ) (h : i + j = n) (x : P.X i) (y : Q.X j) :
    (cochainTensorMap f g).f n ((ιTensorObj P Q i j n h) (x ⊗ₜ[R] y)) =
      (ιTensorObj P' Q' i j n h) (f.f i x ⊗ₜ[R] g.f j y) :=
  congrArg (fun f => f (x ⊗ₜ[R] y)) (ι_mapBifunctorMap f g (curriedTensor _) (.up ℤ) i j n h)

lemma cochainTensorSymmetry_hom_apply_ι
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (i j n : ℤ) (h : i + j = n)
    (x : P.X i) (y : Q.X j) :
    (cochainTensorSymmetry P Q).hom.f n ((ιTensorObj P Q i j n h) (x ⊗ₜ[R] y)) =
      (i * j).negOnePow • ((ιTensorObj Q P j i n (by omega)) (y ⊗ₜ[R] x)) :=
  congrArg (fun f => f (x ⊗ₜ[R] y)) (ιTensorObj_cochainTensorSymmetry P Q i j n h)

abbrev cochainTensorQuadι (P Q T U : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j k l n : ℤ) (h : i + j + k + l = n) :=
  (ιTensorObj P Q i j (i + j) rfl ⊗ₘ ιTensorObj T U k l (k + l) rfl) ≫
    ιTensorObj (cochainTensor P Q) (cochainTensor T U) (i + j) (k + l) n (by omega)

lemma cochainTensorQuad_hom_ext (P Q T U : CochainComplex (ModuleCat.{u} R) ℤ)
    (n : ℤ) {Y : ModuleCat.{u} R}
    {f g : (cochainTensor (cochainTensor P Q) (cochainTensor T U)).X n ⟶ Y}
    (h : ∀ i j k l (hijkl : i + j + k + l = n),
      cochainTensorQuadι P Q T U i j k l n hijkl ≫ f =
        cochainTensorQuadι P Q T U i j k l n hijkl ≫ g) : f = g := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  dsimp at hab
  apply cochainTensorX_whiskerRight_hom_ext P Q a ((cochainTensor T U).X b) Y
  intro i j hij
  apply cochainTensorX_whiskerLeft_hom_ext T U b (P.X i ⊗ Q.X j) Y
  intro k l hkl
  subst a
  subst b
  simp only [← tensorHom_def'_assoc]
  exact h i j k l (by omega)

lemma cochainTensorQuadι_apply (P Q T U : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j k l n : ℤ) (h : i + j + k + l = n)
    (x : P.X i) (y : Q.X j) (z : T.X k) (w : U.X l) :
    cochainTensorQuadι P Q T U i j k l n h ((x ⊗ₜ[R] y) ⊗ₜ[R] (z ⊗ₜ[R] w)) =
      ιTensorObj (cochainTensor P Q) (cochainTensor T U) (i + j) (k + l) n (by omega)
        ((ιTensorObj P Q i j (i + j) rfl) (x ⊗ₜ[R] y) ⊗ₜ[R]
          (ιTensorObj T U k l (k + l) rfl) (z ⊗ₜ[R] w)) := rfl

lemma cochainTensorQuad_apply_of_sum (P Q T U : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j k l a b n : ℤ) (ha : i + j = a) (hb : k + l = b) (h : a + b = n)
    (x : P.X i) (y : Q.X j) (z : T.X k) (w : U.X l) :
    ιTensorObj (cochainTensor P Q) (cochainTensor T U) a b n h
      ((ιTensorObj P Q i j a ha) (x ⊗ₜ[R] y) ⊗ₜ[R]
        (ιTensorObj T U k l b hb) (z ⊗ₜ[R] w)) =
    cochainTensorQuadι P Q T U i j k l n (by omega)
      ((x ⊗ₜ[R] y) ⊗ₜ[R] (z ⊗ₜ[R] w)) := by
  subst a
  subst b
  rfl

lemma cochainTensorQuad_symmetry_apply_ι
    (P Q T U : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j k l n : ℤ) (h : i + j + k + l = n)
    (x : P.X i) (y : Q.X j) (z : T.X k) (w : U.X l) :
    (cochainTensorSymmetry (cochainTensor P Q) (cochainTensor T U)).hom.f n
      (cochainTensorQuadι P Q T U i j k l n h ((x ⊗ₜ[R] y) ⊗ₜ[R] (z ⊗ₜ[R] w))) =
    ((i + j) * (k + l)).negOnePow •
      (cochainTensorQuadι T U P Q k l i j n (by omega) ((z ⊗ₜ[R] w) ⊗ₜ[R] (x ⊗ₜ[R] y))) := by
  rw [cochainTensorQuadι_apply, cochainTensorSymmetry_hom_apply_ι, cochainTensorQuadι_apply]

lemma cochainTensorShuffle_hom_apply_ι
    (P Q T U : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j k l n : ℤ) (h : i + j + k + l = n)
    (x : P.X i) (y : Q.X j) (z : T.X k) (w : U.X l) :
    (cochainTensorShuffle P Q T U).hom.f n
      (cochainTensorQuadι P Q T U i j k l n h ((x ⊗ₜ[R] y) ⊗ₜ[R] (z ⊗ₜ[R] w))) =
    (j * k).negOnePow •
      (cochainTensorQuadι P T Q U i k j l n (by omega) ((x ⊗ₜ[R] z) ⊗ₜ[R] (y ⊗ₜ[R] w))) := by
  change (cochainTensorAssociator P T (cochainTensor Q U)).inv.f n
    ((cochainTensorMap (𝟙 P) (cochainTensorAssociator T Q U).hom).f n
      ((cochainTensorMap (𝟙 P)
        (cochainTensorMap (cochainTensorSymmetry Q T).hom (𝟙 U))).f n
        ((cochainTensorMap (𝟙 P) (cochainTensorAssociator Q T U).inv).f n
          ((cochainTensorAssociator P Q (cochainTensor T U)).hom.f n
            (ιTensorObj (cochainTensor P Q) (cochainTensor T U) (i + j) (k + l) n (by omega)
              ((ιTensorObj P Q i j (i + j) rfl) (x ⊗ₜ[R] y) ⊗ₜ[R]
                (ιTensorObj T U k l (k + l) rfl) (z ⊗ₜ[R] w))))))) = _
  rw [cochainTensorAssociator_hom_apply_ι P Q (cochainTensor T U) i j (k + l) n (by omega)]
  rw [cochainTensorMap_apply_ι]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply]
  rw [cochainTensorAssociator_inv_apply_ι Q T U j k l (j + (k + l)) (by omega)]
  rw [cochainTensorMap_apply_ι]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply]
  rw [cochainTensorMap_apply_ι]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply]
  rw [cochainTensorMap_apply_ι]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply]
  rw [cochainTensorSymmetry_hom_apply_ι]
  simp only [Units.smul_def, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, map_zsmul]
  rw [cochainTensorAssociator_hom_apply_ι_of_sum T Q U k j l (j + k) (j + (k + l))
    (by omega) (by omega)]
  rw [cochainTensorAssociator_inv_apply_ι_of_sum P T (cochainTensor Q U)
    i k (j + l) (j + (k + l)) n (by omega) (by omega)]
  rw [cochainTensorQuadι_apply]

@[reassoc]
lemma ιTensorQuad_cochainTensorShuffle_hom
    (P Q T U : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j k l n : ℤ) (h : i + j + k + l = n) :
    cochainTensorQuadι P Q T U i j k l n h ≫ (cochainTensorShuffle P Q T U).hom.f n =
    (j * k).negOnePow •
      (tensorμ (P.X i) (Q.X j) (T.X k) (U.X l) ≫
        cochainTensorQuadι P T Q U i k j l n (by omega)) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_fourfold'
  intro x y z w
  exact cochainTensorShuffle_hom_apply_ι P Q T U i j k l n h x y z w

end SerrePositivity

end CochainTensorHomogeneousPart

section CochainTensorTriplePart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
open scoped TensorProduct
variable {R : Type u} [CommRing R]

abbrev cochainTensorTripleι (P Q T : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j k n : ℤ) (h : i + j + k = n) :=
  (ιTensorObj P Q i j (i + j) rfl ▷ T.X k) ≫
    ιTensorObj (cochainTensor P Q) T (i + j) k n h

lemma cochainTensorTriple_hom_ext (P Q T : CochainComplex (ModuleCat.{u} R) ℤ)
    (n : ℤ) {Y : ModuleCat.{u} R}
    {f g : (cochainTensor (cochainTensor P Q) T).X n ⟶ Y}
    (h : ∀ i j k (hijk : i + j + k = n),
      cochainTensorTripleι P Q T i j k n hijk ≫ f =
        cochainTensorTripleι P Q T i j k n hijk ≫ g) : f = g := by
  exact HomologicalComplex.mapBifunctor₁₂.hom_ext h

lemma cochainTensorTripleι_apply (P Q T : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j k n : ℤ) (h : i + j + k = n) (x : P.X i) (y : Q.X j) (z : T.X k) :
    cochainTensorTripleι P Q T i j k n h ((x ⊗ₜ[R] y) ⊗ₜ[R] z) =
      ιTensorObj (cochainTensor P Q) T (i + j) k n h
        ((ιTensorObj P Q i j (i + j) rfl) (x ⊗ₜ[R] y) ⊗ₜ[R] z) := rfl

/-- Move the last factor to the front; the signed braiding is followed by reassociation. -/
def cochainTensorRotationIso (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) :
    cochainTensor (cochainTensor P Q) T ≅ cochainTensor (cochainTensor T P) Q :=
  cochainTensorSymmetry (cochainTensor P Q) T ≪≫ (cochainTensorAssociator T P Q).symm

lemma cochainTensorRotation_apply_ι
    (P Q T : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j k n : ℤ) (h : i + j + k = n) (x : P.X i) (y : Q.X j) (z : T.X k) :
    (cochainTensorRotationIso P Q T).hom.f n
      (cochainTensorTripleι P Q T i j k n h ((x ⊗ₜ[R] y) ⊗ₜ[R] z)) =
      ((i + j) * k).negOnePow •
        (cochainTensorTripleι T P Q k i j n (by omega) ((z ⊗ₜ[R] x) ⊗ₜ[R] y)) := by
  change (cochainTensorAssociator T P Q).inv.f n
    ((cochainTensorSymmetry (cochainTensor P Q) T).hom.f n
      (ιTensorObj (cochainTensor P Q) T (i + j) k n h
        ((ιTensorObj P Q i j (i + j) rfl) (x ⊗ₜ[R] y) ⊗ₜ[R] z))) = _
  rw [cochainTensorSymmetry_hom_apply_ι]
  simp only [Units.smul_def, map_zsmul]
  rw [cochainTensorAssociator_inv_apply_ι_of_sum T P Q k i j (i + j) n rfl (by omega)]
  rfl

/-- Three right rotations return every factor and cancel the Koszul signs. -/
lemma cochainTensorRotation_cube (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) :
    (cochainTensorRotationIso P Q T).hom ≫ (cochainTensorRotationIso T P Q).hom ≫
      (cochainTensorRotationIso Q T P).hom = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply cochainTensorTriple_hom_ext P Q T n
  intro i j k h
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro x y z
  change (cochainTensorRotationIso Q T P).hom.f n
    ((cochainTensorRotationIso T P Q).hom.f n
      ((cochainTensorRotationIso P Q T).hom.f n
        (cochainTensorTripleι P Q T i j k n h ((x ⊗ₜ[R] y) ⊗ₜ[R] z)))) =
      cochainTensorTripleι P Q T i j k n h ((x ⊗ₜ[R] y) ⊗ₜ[R] z)
  rw [cochainTensorRotation_apply_ι]
  simp only [Units.smul_def, map_zsmul]
  rw [cochainTensorRotation_apply_ι]
  simp only [Units.smul_def, map_zsmul]
  rw [cochainTensorRotation_apply_ι]
  change ((i + j) * k).negOnePow • (((k + i) * j).negOnePow •
    (((j + k) * i).negOnePow •
      cochainTensorTripleι P Q T i j k n h ((x ⊗ₜ[R] y) ⊗ₜ[R] z))) = _
  have hs : ((i + j) * k).negOnePow * ((k + i) * j).negOnePow *
      ((j + k) * i).negOnePow = 1 := by
    rw [← Int.negOnePow_add, ← Int.negOnePow_add]
    have he : (i + j) * k + (k + i) * j + (j + k) * i =
        2 * (i * j + j * k + i * k) := by ring
    rw [he, Int.negOnePow_two_mul]
  rw [smul_smul, smul_smul, hs, one_smul]

abbrev cochainTensorTripleMap
    {P P' Q Q' T T' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') (t : T ⟶ T') :=
  cochainTensorMap (cochainTensorMap f g) t

lemma cochainTensorTripleMap_apply_ι
    {P P' Q Q' T T' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') (t : T ⟶ T')
    (i j k n : ℤ) (h : i + j + k = n) (x : P.X i) (y : Q.X j) (z : T.X k) :
    (cochainTensorTripleMap f g t).f n
      (cochainTensorTripleι P Q T i j k n h ((x ⊗ₜ[R] y) ⊗ₜ[R] z)) =
      cochainTensorTripleι P' Q' T' i j k n h
        ((f.f i x ⊗ₜ[R] g.f j y) ⊗ₜ[R] t.f k z) := by
  rw [cochainTensorTripleι_apply, cochainTensorMap_apply_ι, cochainTensorMap_apply_ι]
  rfl

@[reassoc]
lemma cochainTensorRotation_naturality
    {P P' Q Q' T T' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') (t : T ⟶ T') :
    cochainTensorTripleMap f g t ≫ (cochainTensorRotationIso P' Q' T').hom =
      (cochainTensorRotationIso P Q T).hom ≫ cochainTensorTripleMap t f g := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply cochainTensorTriple_hom_ext P Q T n
  intro i j k h
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro x y z
  change (cochainTensorRotationIso P' Q' T').hom.f n
    ((cochainTensorTripleMap f g t).f n
      (cochainTensorTripleι P Q T i j k n h ((x ⊗ₜ[R] y) ⊗ₜ[R] z))) =
    (cochainTensorTripleMap t f g).f n
      ((cochainTensorRotationIso P Q T).hom.f n
        (cochainTensorTripleι P Q T i j k n h ((x ⊗ₜ[R] y) ⊗ₜ[R] z)))
  rw [cochainTensorTripleMap_apply_ι, cochainTensorRotation_apply_ι,
    cochainTensorRotation_apply_ι]
  simp only [Units.smul_def, map_zsmul]
  rw [cochainTensorTripleMap_apply_ι]

end SerrePositivity

end CochainTensorTriplePart

section CochainTensorHexagonPart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
open scoped TensorProduct
variable {R : Type u} [CommRing R]

/-- Normalize the intermediate total degree in a right-associated tensor inclusion. -/
lemma cochainTensorRightTriple_apply_of_sum
    (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) (i j k s n : ℤ)
    (hs : j + k = s) (h : i + s = n) (x : P.X i) (y : Q.X j) (z : T.X k) :
    ιTensorObj P (cochainTensor Q T) i s n h
        (x ⊗ₜ[R] ιTensorObj Q T j k s hs (y ⊗ₜ[R] z)) =
      ιTensorObj P (cochainTensor Q T) i (j + k) n (by omega)
        (x ⊗ₜ[R] ιTensorObj Q T j k (j + k) rfl (y ⊗ₜ[R] z)) := by
  subst s
  rfl

/-- The signed tensor symmetry and the standard associator satisfy the first hexagon. -/
lemma cochainTensorSymmetry_hexagon_forward
    (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) :
    (cochainTensorAssociator P Q T).hom ≫
        (cochainTensorSymmetry P (cochainTensor Q T)).hom ≫
        (cochainTensorAssociator Q T P).hom =
      cochainTensorMap (cochainTensorSymmetry P Q).hom (𝟙 T) ≫
        (cochainTensorAssociator Q P T).hom ≫
        cochainTensorMap (𝟙 Q) (cochainTensorSymmetry P T).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply cochainTensorTriple_hom_ext P Q T n
  intro i j k h
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro x y z
  change (cochainTensorAssociator Q T P).hom.f n
      ((cochainTensorSymmetry P (cochainTensor Q T)).hom.f n
        ((cochainTensorAssociator P Q T).hom.f n
          (cochainTensorTripleι P Q T i j k n h ((x ⊗ₜ[R] y) ⊗ₜ[R] z)))) =
    (cochainTensorMap (𝟙 Q) (cochainTensorSymmetry P T).hom).f n
      ((cochainTensorAssociator Q P T).hom.f n
        ((cochainTensorMap (cochainTensorSymmetry P Q).hom (𝟙 T)).f n
          (cochainTensorTripleι P Q T i j k n h ((x ⊗ₜ[R] y) ⊗ₜ[R] z))))
  rw [cochainTensorTripleι_apply, cochainTensorAssociator_hom_apply_ι,
    cochainTensorSymmetry_hom_apply_ι]
  simp only [Units.smul_def, map_zsmul]
  rw [cochainTensorAssociator_hom_apply_ι_of_sum]
  rw [cochainTensorMap_apply_ι, cochainTensorSymmetry_hom_apply_ι]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply, Units.smul_def,
    ← TensorProduct.smul_tmul', map_zsmul]
  rw [cochainTensorAssociator_hom_apply_ι_of_sum, cochainTensorMap_apply_ι,
    cochainTensorSymmetry_hom_apply_ι]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply, Units.smul_def,
    TensorProduct.tmul_smul, map_zsmul, smul_smul]
  simp only [mul_add, Int.negOnePow_add, Units.val_mul]
  rw [cochainTensorRightTriple_apply_of_sum Q T P j k i (i + k) n
    (add_comm k i) (by omega) y z x]

/-- The inverse signed symmetry is the symmetry in the reverse order. -/
@[simp]
lemma cochainTensorSymmetry_inv (P Q : CochainComplex (ModuleCat.{u} R) ℤ) :
    (cochainTensorSymmetry P Q).inv = (cochainTensorSymmetry Q P).hom := by
  apply (cancel_epi (cochainTensorSymmetry P Q).hom).mp
  rw [Iso.hom_inv_id, cochainTensorSymmetry_hom_comp]

end SerrePositivity

end CochainTensorHexagonPart

section CochainTensorBraidedPart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
variable {R : Type u} [CommRing R]

/-- Involutivity and the first hexagon give the second hexagon, with the actual maps. -/
lemma cochainTensorSymmetry_hexagon_reverse
    (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) :
    (cochainTensorAssociator P Q T).inv ≫
        (cochainTensorSymmetry (cochainTensor P Q) T).hom ≫
        (cochainTensorAssociator T P Q).inv =
      cochainTensorMap (𝟙 P) (cochainTensorSymmetry Q T).hom ≫
        (cochainTensorAssociator P T Q).inv ≫
        cochainTensorMap (cochainTensorSymmetry P T).hom (𝟙 Q) := by
  have h :
      cochainTensorAssociator T P Q ≪≫ cochainTensorSymmetry T (cochainTensor P Q) ≪≫
          cochainTensorAssociator P Q T =
        cochainTensorIso (cochainTensorSymmetry T P) (Iso.refl Q) ≪≫
          cochainTensorAssociator P T Q ≪≫
          cochainTensorIso (Iso.refl P) (cochainTensorSymmetry T Q) := by
    apply Iso.ext
    exact cochainTensorSymmetry_hexagon_forward T P Q
  have hi := congrArg Iso.inv h
  simp only [Iso.trans_inv, cochainTensorIso, MonoidalCategory.tensorIso_inv,
    Iso.refl_inv, cochainTensorSymmetry_inv, Category.assoc] at hi
  exact hi

/-- The existing cochain tensor is symmetric monoidal with its actual Koszul-signed symmetry. -/
instance cochainTensorSymmetricCategory :
    SymmetricCategory (CochainComplex (ModuleCat.{u} R) ℤ) where
  braiding := cochainTensorSymmetry
  braiding_naturality_right := by
    intro P Q T f
    exact cochainTensorSymmetry_naturality (𝟙 P) f
  braiding_naturality_left := by
    intro P Q f T
    exact cochainTensorSymmetry_naturality f (𝟙 T)
  hexagon_forward := cochainTensorSymmetry_hexagon_forward
  hexagon_reverse := cochainTensorSymmetry_hexagon_reverse
  symmetry := cochainTensorSymmetry_hom_comp

end SerrePositivity

end CochainTensorBraidedPart

section CochainTensorShuffleEquivariancePart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
open scoped TensorProduct
variable {R : Type u} [CommRing R]

lemma cochainTensorQuad_diagonalSymmetry_apply_ι
    (P Q T U : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j k l n : ℤ) (h : i + j + k + l = n)
    (x : P.X i) (y : Q.X j) (z : T.X k) (w : U.X l) :
    (cochainTensorMap (cochainTensorSymmetry P Q).hom (cochainTensorSymmetry T U).hom).f n
      (cochainTensorQuadι P Q T U i j k l n h ((x ⊗ₜ[R] y) ⊗ₜ[R] (z ⊗ₜ[R] w))) =
    (i * j + k * l).negOnePow •
      (cochainTensorQuadι Q P U T j i l k n (by omega) ((y ⊗ₜ[R] x) ⊗ₜ[R] (w ⊗ₜ[R] z))) := by
  rw [cochainTensorQuadι_apply, cochainTensorMap_apply_ι,
    cochainTensorSymmetry_hom_apply_ι, cochainTensorSymmetry_hom_apply_ι]
  simp only [Units.smul_def, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul,
    map_zsmul, smul_smul, Int.negOnePow_add, Units.val_mul]
  rw [cochainTensorQuad_apply_of_sum]
  rw [mul_comm ((k * l).negOnePow : ℤ) ((i * j).negOnePow : ℤ)]

lemma cochainTensorShuffle_exchange_sign (i j k l : ℤ) :
    ((i + j) * (k + l)).negOnePow * (l * i).negOnePow =
      (j * k).negOnePow * (i * k + j * l).negOnePow := by
  rw [← Int.negOnePow_add, ← Int.negOnePow_add]
  have he : (i + j) * (k + l) + l * i = (j * k + (i * k + j * l)) + 2 * (i * l) := by
    ring
  rw [he, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]

lemma cochainTensorShuffle_symmetry
    (P Q T U : CochainComplex (ModuleCat.{u} R) ℤ) :
    (cochainTensorSymmetry (cochainTensor P Q) (cochainTensor T U)).hom ≫
      (cochainTensorShuffle T U P Q).hom =
    (cochainTensorShuffle P Q T U).hom ≫
      cochainTensorMap (cochainTensorSymmetry P T).hom (cochainTensorSymmetry Q U).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply cochainTensorQuad_hom_ext P Q T U n
  intro i j k l h
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_fourfold'
  intro x y z w
  change (cochainTensorShuffle T U P Q).hom.f n
      ((cochainTensorSymmetry (cochainTensor P Q) (cochainTensor T U)).hom.f n
        (cochainTensorQuadι P Q T U i j k l n h ((x ⊗ₜ[R] y) ⊗ₜ[R] (z ⊗ₜ[R] w)))) =
    (cochainTensorMap (cochainTensorSymmetry P T).hom (cochainTensorSymmetry Q U).hom).f n
      ((cochainTensorShuffle P Q T U).hom.f n
        (cochainTensorQuadι P Q T U i j k l n h ((x ⊗ₜ[R] y) ⊗ₜ[R] (z ⊗ₜ[R] w))))
  rw [cochainTensorQuad_symmetry_apply_ι]
  simp only [Units.smul_def, map_zsmul]
  rw [cochainTensorShuffle_hom_apply_ι, cochainTensorShuffle_hom_apply_ι]
  simp only [Units.smul_def, map_zsmul]
  rw [cochainTensorQuad_diagonalSymmetry_apply_ι]
  simpa only [Units.smul_def, smul_smul, Units.val_mul] using
    congrArg (fun r : ℤˣ => r •
      (cochainTensorQuadι T P U Q k i l j n (by omega)
        ((z ⊗ₜ[R] x) ⊗ₜ[R] (w ⊗ₜ[R] y))))
      (cochainTensorShuffle_exchange_sign i j k l)

end SerrePositivity

end CochainTensorShuffleEquivariancePart

section CochainTensorTripleDifferentialPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
open scoped TensorProduct
variable {R : Type u} [CommRing R]

lemma cochainTensorTripleι_apply_of_sum (P Q T : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j k s n : ℤ) (hs : i + j = s) (h : s + k = n)
    (x : P.X i) (y : Q.X j) (z : T.X k) :
    cochainTensorTripleι P Q T i j k n (by omega) ((x ⊗ₜ[R] y) ⊗ₜ[R] z) =
      ιTensorObj (cochainTensor P Q) T s k n h
        (ιTensorObj P Q i j s hs (x ⊗ₜ[R] y) ⊗ₜ[R] z) := by
  subst hs
  rfl

lemma cochainTensorTriple_d_apply_ι (P Q T : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j k n : ℤ) (h : i + j + k = n) (x : P.X i) (y : Q.X j) (z : T.X k) :
    (cochainTensor (cochainTensor P Q) T).d n (n + 1)
        (cochainTensorTripleι P Q T i j k n h ((x ⊗ₜ[R] y) ⊗ₜ[R] z)) =
      cochainTensorTripleι P Q T (i + 1) j k (n + 1) (by omega)
        ((P.d i (i + 1) x ⊗ₜ[R] y) ⊗ₜ[R] z) +
      i.negOnePow • cochainTensorTripleι P Q T i (j + 1) k (n + 1) (by omega)
        ((x ⊗ₜ[R] Q.d j (j + 1) y) ⊗ₜ[R] z) +
      (i + j).negOnePow • cochainTensorTripleι P Q T i j (k + 1) (n + 1) (by omega)
        ((x ⊗ₜ[R] y) ⊗ₜ[R] T.d k (k + 1) z) := by
  rw [cochainTensorTripleι_apply, cochainTensor_d_apply_ι, cochainTensor_d_apply_ι]
  simp only [TensorProduct.add_tmul, map_add, Units.smul_def,
    ← TensorProduct.smul_tmul', map_zsmul]
  rw [cochainTensorTripleι_apply_of_sum P Q T (i + 1) j k (i + j + 1) (n + 1)
    (by omega) (by omega),
    cochainTensorTripleι_apply_of_sum P Q T i (j + 1) k (i + j + 1) (n + 1)
      (by omega) (by omega), cochainTensorTripleι_apply]

end SerrePositivity

end CochainTensorTripleDifferentialPart

section CochainTensorScalarCoordinatesPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
open scoped TensorProduct
variable {R : Type u} [CommRing R]

/-- Select one bidegree and apply its two scalar coordinates. -/
def cochainTensorScalarCoordinate (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (i₀ j₀ : ℤ) (f : P.X i₀ ⟶ ModuleCat.of R R) (g : Q.X j₀ ⟶ ModuleCat.of R R)
    (n : ℤ) : (cochainTensor P Q).X n ⟶ ModuleCat.of R R :=
  HomologicalComplex₂.totalDesc _ (fun i j h => by
    by_cases hi : i = i₀
    · subst i
      by_cases hj : j = j₀
      · subst j
        exact (f ⊗ₘ g) ≫ (λ_ (ModuleCat.of R R)).hom
      · exact 0
    · exact 0)

@[reassoc]
lemma ι_cochainTensorScalarCoordinate_match (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (i₀ j₀ n : ℤ) (h : i₀ + j₀ = n)
    (f : P.X i₀ ⟶ ModuleCat.of R R) (g : Q.X j₀ ⟶ ModuleCat.of R R) :
    ιTensorObj P Q i₀ j₀ n h ≫ cochainTensorScalarCoordinate P Q i₀ j₀ f g n =
      (f ⊗ₘ g) ≫ (λ_ (ModuleCat.of R R)).hom := by
  simp [cochainTensorScalarCoordinate]

@[reassoc]
lemma ι_cochainTensorScalarCoordinate_other (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (i₀ j₀ i j n : ℤ) (h : i + j = n)
    (f : P.X i₀ ⟶ ModuleCat.of R R) (g : Q.X j₀ ⟶ ModuleCat.of R R)
    (hne : i ≠ i₀ ∨ j ≠ j₀) :
    ιTensorObj P Q i j n h ≫ cochainTensorScalarCoordinate P Q i₀ j₀ f g n = 0 := by
  by_cases hi : i = i₀
  · subst i
    have hj : j ≠ j₀ := hne.resolve_left (not_not.mpr rfl)
    simp [cochainTensorScalarCoordinate, hj]
  · simp [cochainTensorScalarCoordinate, hi]

lemma cochainTensorScalarCoordinate_apply_match (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (i₀ j₀ n : ℤ) (h : i₀ + j₀ = n)
    (f : P.X i₀ ⟶ ModuleCat.of R R) (g : Q.X j₀ ⟶ ModuleCat.of R R)
    (x : P.X i₀) (y : Q.X j₀) :
    cochainTensorScalarCoordinate P Q i₀ j₀ f g n (ιTensorObj P Q i₀ j₀ n h (x ⊗ₜ[R] y)) =
      f x * g y :=
  congrArg (fun α => α (x ⊗ₜ[R] y)) (ι_cochainTensorScalarCoordinate_match P Q i₀ j₀ n h f g)

lemma cochainTensorScalarCoordinate_apply_other (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (i₀ j₀ i j n : ℤ) (h : i + j = n)
    (f : P.X i₀ ⟶ ModuleCat.of R R) (g : Q.X j₀ ⟶ ModuleCat.of R R)
    (hne : i ≠ i₀ ∨ j ≠ j₀) (x : P.X i) (y : Q.X j) :
    cochainTensorScalarCoordinate P Q i₀ j₀ f g n (ιTensorObj P Q i j n h (x ⊗ₜ[R] y)) = 0 :=
  congrArg (fun α => α (x ⊗ₜ[R] y))
    (ι_cochainTensorScalarCoordinate_other P Q i₀ j₀ i j n h f g hne)

/-- Select a tridegree and multiply the three scalar coordinates. -/
def cochainTensorTripleScalarCoordinate (P Q T : CochainComplex (ModuleCat.{u} R) ℤ)
    (i₀ j₀ k₀ : ℤ) (f : P.X i₀ ⟶ ModuleCat.of R R)
    (g : Q.X j₀ ⟶ ModuleCat.of R R) (e : T.X k₀ ⟶ ModuleCat.of R R)
    (n : ℤ) : (cochainTensor (cochainTensor P Q) T).X n ⟶ ModuleCat.of R R :=
  HomologicalComplex₂.totalDesc _ (fun s k h => by
    by_cases hk : k = k₀
    · subst k
      exact (cochainTensorScalarCoordinate P Q i₀ j₀ f g s ⊗ₘ e) ≫
        (λ_ (ModuleCat.of R R)).hom
    · exact 0)

lemma cochainTensorTripleScalarCoordinate_apply_outer_match
    (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) (i₀ j₀ k₀ s n : ℤ) (h : s + k₀ = n)
    (f : P.X i₀ ⟶ ModuleCat.of R R) (g : Q.X j₀ ⟶ ModuleCat.of R R)
    (e : T.X k₀ ⟶ ModuleCat.of R R) (w : (cochainTensor P Q).X s) (z : T.X k₀) :
    cochainTensorTripleScalarCoordinate P Q T i₀ j₀ k₀ f g e n
        (ιTensorObj (cochainTensor P Q) T s k₀ n h (w ⊗ₜ[R] z)) =
      cochainTensorScalarCoordinate P Q i₀ j₀ f g s w * e z := by
  have he : ιTensorObj (cochainTensor P Q) T s k₀ n h ≫
      cochainTensorTripleScalarCoordinate P Q T i₀ j₀ k₀ f g e n =
      (cochainTensorScalarCoordinate P Q i₀ j₀ f g s ⊗ₘ e) ≫
        (λ_ (ModuleCat.of R R)).hom := by simp [cochainTensorTripleScalarCoordinate]
  exact congrArg (fun α => α (w ⊗ₜ[R] z)) he

lemma cochainTensorTripleScalarCoordinate_apply_outer_other
    (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) (i₀ j₀ k₀ s k n : ℤ) (h : s + k = n)
    (f : P.X i₀ ⟶ ModuleCat.of R R) (g : Q.X j₀ ⟶ ModuleCat.of R R)
    (e : T.X k₀ ⟶ ModuleCat.of R R) (hk : k ≠ k₀)
    (w : (cochainTensor P Q).X s) (z : T.X k) :
    cochainTensorTripleScalarCoordinate P Q T i₀ j₀ k₀ f g e n
      (ιTensorObj (cochainTensor P Q) T s k n h (w ⊗ₜ[R] z)) = 0 := by
  have he : ιTensorObj (cochainTensor P Q) T s k n h ≫
      cochainTensorTripleScalarCoordinate P Q T i₀ j₀ k₀ f g e n = 0 := by
    simp [cochainTensorTripleScalarCoordinate, hk]
  exact congrArg (fun α => α (w ⊗ₜ[R] z)) he

lemma cochainTensorTripleScalarCoordinate_apply_match
    (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) (i₀ j₀ k₀ n : ℤ) (h : i₀ + j₀ + k₀ = n)
    (f : P.X i₀ ⟶ ModuleCat.of R R) (g : Q.X j₀ ⟶ ModuleCat.of R R)
    (e : T.X k₀ ⟶ ModuleCat.of R R) (x : P.X i₀) (y : Q.X j₀) (z : T.X k₀) :
    cochainTensorTripleScalarCoordinate P Q T i₀ j₀ k₀ f g e n
      (cochainTensorTripleι P Q T i₀ j₀ k₀ n h ((x ⊗ₜ[R] y) ⊗ₜ[R] z)) =
      (f x * g y) * e z := by
  rw [cochainTensorTripleι_apply, cochainTensorTripleScalarCoordinate_apply_outer_match,
    cochainTensorScalarCoordinate_apply_match]

lemma cochainTensorTripleScalarCoordinate_apply_other
    (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) (i₀ j₀ k₀ i j k n : ℤ) (h : i + j + k = n)
    (f : P.X i₀ ⟶ ModuleCat.of R R) (g : Q.X j₀ ⟶ ModuleCat.of R R)
    (e : T.X k₀ ⟶ ModuleCat.of R R) (hne : i ≠ i₀ ∨ j ≠ j₀ ∨ k ≠ k₀)
    (x : P.X i) (y : Q.X j) (z : T.X k) :
    cochainTensorTripleScalarCoordinate P Q T i₀ j₀ k₀ f g e n
      (cochainTensorTripleι P Q T i j k n h ((x ⊗ₜ[R] y) ⊗ₜ[R] z)) = 0 := by
  rw [cochainTensorTripleι_apply]
  by_cases hk : k = k₀
  · subst k
    rw [cochainTensorTripleScalarCoordinate_apply_outer_match,
      cochainTensorScalarCoordinate_apply_other P Q i₀ j₀ i j (i + j) rfl f g (by tauto), zero_mul]
  · exact cochainTensorTripleScalarCoordinate_apply_outer_other P Q T i₀ j₀ k₀ (i + j) k n h
      f g e hk _ z

end SerrePositivity

end CochainTensorScalarCoordinatesPart

section CochainTensorSixShufflePart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
open scoped TensorProduct
variable {R : Type u} [CommRing R]

/-- Two four-factor shuffles separate the first and second entries of three pairs. -/
def cochainTensorSixShuffle (P Q T U V W : CochainComplex (ModuleCat.{u} R) ℤ) :
    cochainTensor (cochainTensor (cochainTensor P Q) (cochainTensor T U)) (cochainTensor V W) ≅
      cochainTensor (cochainTensor (cochainTensor P T) V) (cochainTensor (cochainTensor Q U) W) :=
  cochainTensorIso (cochainTensorShuffle P Q T U) (Iso.refl (cochainTensor V W)) ≪≫
    cochainTensorShuffle (cochainTensor P T) (cochainTensor Q U) V W

abbrev cochainTensorSixι (P Q T U V W : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j k l a b n : ℤ) (h : i + j + k + l + a + b = n) :=
  (cochainTensorQuadι P Q T U i j k l (i + j + k + l) rfl ⊗ₘ
    ιTensorObj V W a b (a + b) rfl) ≫
      ιTensorObj (cochainTensor (cochainTensor P Q) (cochainTensor T U)) (cochainTensor V W)
        (i + j + k + l) (a + b) n (by omega)

abbrev cochainTensorSixSeparatedι (P T V Q U W : CochainComplex (ModuleCat.{u} R) ℤ)
    (i k a j l b n : ℤ) (h : i + k + a + j + l + b = n) :=
  (cochainTensorTripleι P T V i k a (i + k + a) rfl ⊗ₘ
    cochainTensorTripleι Q U W j l b (j + l + b) rfl) ≫
      ιTensorObj (cochainTensor (cochainTensor P T) V) (cochainTensor (cochainTensor Q U) W)
        (i + k + a) (j + l + b) n (by omega)

lemma cochainTensorSixShuffle_hom_apply_ι
    (P Q T U V W : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j k l a b n : ℤ) (h : i + j + k + l + a + b = n)
    (x : P.X i) (y : Q.X j) (z : T.X k) (w : U.X l) (v : V.X a) (r : W.X b) :
    (cochainTensorSixShuffle P Q T U V W).hom.f n
      (cochainTensorSixι P Q T U V W i j k l a b n h
        (((x ⊗ₜ[R] y) ⊗ₜ[R] (z ⊗ₜ[R] w)) ⊗ₜ[R] (v ⊗ₜ[R] r))) =
      (j * k + (j + l) * a).negOnePow •
        (cochainTensorSixSeparatedι P T V Q U W i k a j l b n (by omega)
          (((x ⊗ₜ[R] z) ⊗ₜ[R] v) ⊗ₜ[R] ((y ⊗ₜ[R] w) ⊗ₜ[R] r))) := by
  change (cochainTensorShuffle (cochainTensor P T) (cochainTensor Q U) V W).hom.f n
    ((cochainTensorMap (cochainTensorShuffle P Q T U).hom (𝟙 (cochainTensor V W))).f n
      (ιTensorObj (cochainTensor (cochainTensor P Q) (cochainTensor T U)) (cochainTensor V W)
        (i + j + k + l) (a + b) n (by omega)
        (cochainTensorQuadι P Q T U i j k l (i + j + k + l) rfl
          ((x ⊗ₜ[R] y) ⊗ₜ[R] (z ⊗ₜ[R] w)) ⊗ₜ[R]
            (ιTensorObj V W a b (a + b) rfl) (v ⊗ₜ[R] r)))) = _
  rw [cochainTensorMap_apply_ι, cochainTensorShuffle_hom_apply_ι]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply, Units.smul_def,
    ← TensorProduct.smul_tmul', map_zsmul]
  rw [cochainTensorQuadι_apply]
  rw [cochainTensorQuad_apply_of_sum (cochainTensor P T) (cochainTensor Q U) V W
    (i + k) (j + l) a b (i + j + k + l) (a + b) n (by omega) rfl (by omega)]
  rw [cochainTensorShuffle_hom_apply_ι]
  simp only [Units.smul_def, smul_smul, Int.negOnePow_add, Units.val_mul]
  rw [cochainTensorQuadι_apply]
  rfl

/-- The shuffle signs agree after rotating all three pairs or the two separate triples. -/
lemma cochainTensorSixShuffle_rotation_sign (i j k l a b : ℤ) :
    ((i + j + k + l) * (a + b)).negOnePow * (b * i + (b + j) * k).negOnePow =
      (j * k + (j + l) * a).negOnePow * ((i + k) * a + (j + l) * b).negOnePow := by
  rw [← Int.negOnePow_add, ← Int.negOnePow_add]
  have h : (i + j + k + l) * (a + b) + (b * i + (b + j) * k) =
      (j * k + (j + l) * a + ((i + k) * a + (j + l) * b)) + 2 * (b * (i + k)) := by ring
  rw [h, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]

end SerrePositivity

end CochainTensorSixShufflePart

section CochainTensorSixHomogeneousPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
open scoped TensorProduct
variable {R : Type u} [CommRing R]

lemma cochainTensorX_whiskerRight_twice_hom_ext
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) (T U Y : ModuleCat.{u} R)
    {f g : ((cochainTensor P Q).X n ⊗ T) ⊗ U ⟶ Y}
    (h : ∀ i j (hij : i + j = n), ((ιTensorObj P Q i j n hij ▷ T) ▷ U) ≫ f =
      ((ιTensorObj P Q i j n hij ▷ T) ▷ U) ≫ g) : f = g := by
  apply (isColimitOfHasCoproductOfPreservesColimit
    (tensorRight T ⋙ tensorRight U) (cochainTensorSummand P Q n)).hom_ext
  intro ij
  exact h ij.as.val.1 ij.as.val.2 ij.as.property

lemma cochainTensorX_whiskerLeft_right_hom_ext
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) (T U Y : ModuleCat.{u} R)
    {f g : (T ⊗ (cochainTensor P Q).X n) ⊗ U ⟶ Y}
    (h : ∀ i j (hij : i + j = n), ((T ◁ ιTensorObj P Q i j n hij) ▷ U) ≫ f =
      ((T ◁ ιTensorObj P Q i j n hij) ▷ U) ≫ g) : f = g := by
  apply (isColimitOfHasCoproductOfPreservesColimit
    (tensorLeft T ⋙ tensorRight U) (cochainTensorSummand P Q n)).hom_ext
  intro ij
  exact h ij.as.val.1 ij.as.val.2 ij.as.property

lemma cochainTensorSix_hom_ext (P Q T U V W : CochainComplex (ModuleCat.{u} R) ℤ)
    (n : ℤ) {Y : ModuleCat.{u} R}
    {f g : (cochainTensor (cochainTensor (cochainTensor P Q) (cochainTensor T U))
      (cochainTensor V W)).X n ⟶ Y}
    (h : ∀ i j k l a b (hijklab : i + j + k + l + a + b = n),
      cochainTensorSixι P Q T U V W i j k l a b n hijklab ≫ f =
        cochainTensorSixι P Q T U V W i j k l a b n hijklab ≫ g) : f = g := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro s c hsc
  dsimp at hsc
  apply cochainTensorX_whiskerRight_hom_ext (cochainTensor P Q) (cochainTensor T U)
    s ((cochainTensor V W).X c) Y
  intro d e hde
  apply cochainTensorX_whiskerRight_twice_hom_ext P Q d ((cochainTensor T U).X e)
    ((cochainTensor V W).X c) Y
  intro i j hij
  apply cochainTensorX_whiskerLeft_right_hom_ext T U e (P.X i ⊗ Q.X j)
    ((cochainTensor V W).X c) Y
  intro k l hkl
  apply cochainTensorX_whiskerLeft_hom_ext V W c ((P.X i ⊗ Q.X j) ⊗ (T.X k ⊗ U.X l)) Y
  intro a b hab
  subst d
  subst e
  subst c
  have hs : s = i + j + k + l := by omega
  subst hs
  simp only [← comp_whiskerRight_assoc, ← tensorHom_def'_assoc]
  exact h i j k l a b (by omega)

/-- Six pure factors determine a linear map out of three paired tensors. -/
lemma tensorProductSix_ext_pairs
    {A B C D E F G : Type u}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
    [AddCommGroup E] [AddCommGroup F] [AddCommGroup G]
    [Module R A] [Module R B] [Module R C] [Module R D]
    [Module R E] [Module R F] [Module R G]
    {f g : ((A ⊗[R] B) ⊗[R] (C ⊗[R] D)) ⊗[R] (E ⊗[R] F) →ₗ[R] G}
    (h : ∀ a b c d e r, f (((a ⊗ₜ[R] b) ⊗ₜ[R] (c ⊗ₜ[R] d)) ⊗ₜ[R] (e ⊗ₜ[R] r)) =
      g (((a ⊗ₜ[R] b) ⊗ₜ[R] (c ⊗ₜ[R] d)) ⊗ₜ[R] (e ⊗ₜ[R] r))) : f = g := by
  apply TensorProduct.ext'
  intro p q
  have hL : f.comp ((TensorProduct.mk R ((A ⊗[R] B) ⊗[R] (C ⊗[R] D))
      (E ⊗[R] F)).flip q) =
      g.comp ((TensorProduct.mk R ((A ⊗[R] B) ⊗[R] (C ⊗[R] D)) (E ⊗[R] F)).flip q) := by
    apply TensorProduct.ext_fourfold'
    intro a b c d
    have hR : f.comp (TensorProduct.mk R ((A ⊗[R] B) ⊗[R] (C ⊗[R] D)) (E ⊗[R] F)
        ((a ⊗ₜ[R] b) ⊗ₜ[R] (c ⊗ₜ[R] d))) =
        g.comp (TensorProduct.mk R ((A ⊗[R] B) ⊗[R] (C ⊗[R] D)) (E ⊗[R] F)
          ((a ⊗ₜ[R] b) ⊗ₜ[R] (c ⊗ₜ[R] d))) := by
      apply TensorProduct.ext'
      intro e r
      exact h a b c d e r
    exact congrArg (fun k : E ⊗[R] F →ₗ[R] G => k q) hR
  exact congrArg (fun k : (A ⊗[R] B) ⊗[R] (C ⊗[R] D) →ₗ[R] G => k p) hL

end SerrePositivity

end CochainTensorSixHomogeneousPart

section CochainTensorSixRotationPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
open scoped TensorProduct
variable {R : Type u} [CommRing R]

lemma cochainTensorRotation_apply_ι_of_sum
    (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) (i j k s n : ℤ)
    (hs : i + j = s) (h : s + k = n) (x : P.X i) (y : Q.X j) (z : T.X k) :
    (cochainTensorRotationIso P Q T).hom.f n
      (ιTensorObj (cochainTensor P Q) T s k n h
        ((ιTensorObj P Q i j s hs) (x ⊗ₜ[R] y) ⊗ₜ[R] z)) =
      (s * k).negOnePow •
        (cochainTensorTripleι T P Q k i j n (by omega) ((z ⊗ₜ[R] x) ⊗ₜ[R] y)) := by
  subst hs
  exact cochainTensorRotation_apply_ι P Q T i j k n h x y z

lemma cochainTensorSix_apply_of_sum
    (P Q T U V W : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j k l a b s r n : ℤ) (hs : i + j + k + l = s) (hr : a + b = r) (h : s + r = n)
    (x : P.X i) (y : Q.X j) (z : T.X k) (w : U.X l) (v : V.X a) (e : W.X b) :
    ιTensorObj (cochainTensor (cochainTensor P Q) (cochainTensor T U)) (cochainTensor V W)
      s r n h (cochainTensorQuadι P Q T U i j k l s hs
        ((x ⊗ₜ[R] y) ⊗ₜ[R] (z ⊗ₜ[R] w)) ⊗ₜ[R]
          (ιTensorObj V W a b r hr) (v ⊗ₜ[R] e)) =
      cochainTensorSixι P Q T U V W i j k l a b n (by omega)
        (((x ⊗ₜ[R] y) ⊗ₜ[R] (z ⊗ₜ[R] w)) ⊗ₜ[R] (v ⊗ₜ[R] e)) := by
  subst hs
  subst hr
  rfl

lemma cochainTensorSixSeparated_apply_of_sum
    (P T V Q U W : CochainComplex (ModuleCat.{u} R) ℤ)
    (i k a j l b s r n : ℤ) (hs : i + k + a = s) (hr : j + l + b = r) (h : s + r = n)
    (x : P.X i) (z : T.X k) (v : V.X a) (y : Q.X j) (w : U.X l) (e : W.X b) :
    ιTensorObj (cochainTensor (cochainTensor P T) V) (cochainTensor (cochainTensor Q U) W)
      s r n h (cochainTensorTripleι P T V i k a s hs ((x ⊗ₜ[R] z) ⊗ₜ[R] v) ⊗ₜ[R]
        cochainTensorTripleι Q U W j l b r hr ((y ⊗ₜ[R] w) ⊗ₜ[R] e)) =
      cochainTensorSixSeparatedι P T V Q U W i k a j l b n (by omega)
        (((x ⊗ₜ[R] z) ⊗ₜ[R] v) ⊗ₜ[R] ((y ⊗ₜ[R] w) ⊗ₜ[R] e)) := by
  subst hs
  subst hr
  rfl

lemma cochainTensorSix_sourceRotation_apply_ι
    (P Q T U V W : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j k l a b n : ℤ) (h : i + j + k + l + a + b = n)
    (x : P.X i) (y : Q.X j) (z : T.X k) (w : U.X l) (v : V.X a) (e : W.X b) :
    (cochainTensorRotationIso (cochainTensor P Q) (cochainTensor T U)
      (cochainTensor V W)).hom.f n
      (cochainTensorSixι P Q T U V W i j k l a b n h
        (((x ⊗ₜ[R] y) ⊗ₜ[R] (z ⊗ₜ[R] w)) ⊗ₜ[R] (v ⊗ₜ[R] e))) =
      ((i + j + k + l) * (a + b)).negOnePow •
        (cochainTensorSixι V W P Q T U a b i j k l n (by omega)
          (((v ⊗ₜ[R] e) ⊗ₜ[R] (x ⊗ₜ[R] y)) ⊗ₜ[R] (z ⊗ₜ[R] w))) := by
  change (cochainTensorRotationIso (cochainTensor P Q) (cochainTensor T U)
    (cochainTensor V W)).hom.f n
    (ιTensorObj (cochainTensor (cochainTensor P Q) (cochainTensor T U)) (cochainTensor V W)
      (i + j + k + l) (a + b) n (by omega)
      (cochainTensorQuadι P Q T U i j k l (i + j + k + l) rfl
        ((x ⊗ₜ[R] y) ⊗ₜ[R] (z ⊗ₜ[R] w)) ⊗ₜ[R]
          (ιTensorObj V W a b (a + b) rfl) (v ⊗ₜ[R] e))) = _
  rw [cochainTensorQuadι_apply, cochainTensorRotation_apply_ι_of_sum]
  rw [cochainTensorTripleι_apply]
  rw [cochainTensorQuad_apply_of_sum V W P Q a b i j (a + b) (i + j)
    (a + b + (i + j)) rfl rfl rfl]
  rw [cochainTensorSix_apply_of_sum]

lemma cochainTensorSix_diagonalRotation_apply_ι
    (P T V Q U W : CochainComplex (ModuleCat.{u} R) ℤ)
    (i k a j l b n : ℤ) (h : i + k + a + j + l + b = n)
    (x : P.X i) (z : T.X k) (v : V.X a) (y : Q.X j) (w : U.X l) (e : W.X b) :
    (cochainTensorMap (cochainTensorRotationIso P T V).hom
      (cochainTensorRotationIso Q U W).hom).f n
      (cochainTensorSixSeparatedι P T V Q U W i k a j l b n h
        (((x ⊗ₜ[R] z) ⊗ₜ[R] v) ⊗ₜ[R] ((y ⊗ₜ[R] w) ⊗ₜ[R] e))) =
      ((i + k) * a + (j + l) * b).negOnePow •
        (cochainTensorSixSeparatedι V P T W Q U a i k b j l n (by omega)
          (((v ⊗ₜ[R] x) ⊗ₜ[R] z) ⊗ₜ[R] ((e ⊗ₜ[R] y) ⊗ₜ[R] w))) := by
  change (cochainTensorMap (cochainTensorRotationIso P T V).hom
    (cochainTensorRotationIso Q U W).hom).f n
    (ιTensorObj (cochainTensor (cochainTensor P T) V) (cochainTensor (cochainTensor Q U) W)
      (i + k + a) (j + l + b) n (by omega)
      (cochainTensorTripleι P T V i k a (i + k + a) rfl ((x ⊗ₜ[R] z) ⊗ₜ[R] v) ⊗ₜ[R]
        cochainTensorTripleι Q U W j l b (j + l + b) rfl ((y ⊗ₜ[R] w) ⊗ₜ[R] e))) = _
  rw [cochainTensorMap_apply_ι, cochainTensorRotation_apply_ι, cochainTensorRotation_apply_ι]
  simp only [Units.smul_def, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul,
    map_zsmul, smul_smul, Int.negOnePow_add, Units.val_mul]
  rw [cochainTensorSixSeparated_apply_of_sum]
  rw [mul_comm (((j + l) * b).negOnePow : ℤ) (((i + k) * a).negOnePow : ℤ)]

end SerrePositivity

end CochainTensorSixRotationPart

section CochainTensorSixShuffleEquivariancePart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
open scoped TensorProduct
variable {R : Type u} [CommRing R]

@[reassoc]
lemma cochainTensorSixShuffle_rotation
    (P Q T U V W : CochainComplex (ModuleCat.{u} R) ℤ) :
    (cochainTensorRotationIso (cochainTensor P Q) (cochainTensor T U) (cochainTensor V W)).hom ≫
      (cochainTensorSixShuffle V W P Q T U).hom =
    (cochainTensorSixShuffle P Q T U V W).hom ≫
      cochainTensorMap (cochainTensorRotationIso P T V).hom
        (cochainTensorRotationIso Q U W).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply cochainTensorSix_hom_ext P Q T U V W n
  intro i j k l a b h
  apply ModuleCat.hom_ext
  apply tensorProductSix_ext_pairs
  intro x y z w v e
  change (cochainTensorSixShuffle V W P Q T U).hom.f n
    ((cochainTensorRotationIso (cochainTensor P Q) (cochainTensor T U)
      (cochainTensor V W)).hom.f n
      (cochainTensorSixι P Q T U V W i j k l a b n h
        (((x ⊗ₜ[R] y) ⊗ₜ[R] (z ⊗ₜ[R] w)) ⊗ₜ[R] (v ⊗ₜ[R] e)))) =
    (cochainTensorMap (cochainTensorRotationIso P T V).hom
      (cochainTensorRotationIso Q U W).hom).f n
      ((cochainTensorSixShuffle P Q T U V W).hom.f n
        (cochainTensorSixι P Q T U V W i j k l a b n h
          (((x ⊗ₜ[R] y) ⊗ₜ[R] (z ⊗ₜ[R] w)) ⊗ₜ[R] (v ⊗ₜ[R] e))))
  rw [cochainTensorSix_sourceRotation_apply_ι]
  simp only [Units.smul_def, map_zsmul]
  rw [cochainTensorSixShuffle_hom_apply_ι, cochainTensorSixShuffle_hom_apply_ι]
  simp only [Units.smul_def, map_zsmul]
  rw [cochainTensorSix_diagonalRotation_apply_ι]
  simpa only [Units.smul_def, smul_smul, Units.val_mul] using
    congrArg (fun r : ℤˣ => r •
      (cochainTensorSixSeparatedι V P T W Q U a i k b j l n (by omega)
        (((v ⊗ₜ[R] x) ⊗ₜ[R] z) ⊗ₜ[R] ((e ⊗ₜ[R] y) ⊗ₜ[R] w))))
      (cochainTensorSixShuffle_rotation_sign i j k l a b)

end SerrePositivity

end CochainTensorSixShuffleEquivariancePart
