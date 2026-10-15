module

public import SerrePositivity.HomologicalAlgebra.CochainTensorShuffle

/-! # Homogeneous element formulas for cochain tensor comparisons -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
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
