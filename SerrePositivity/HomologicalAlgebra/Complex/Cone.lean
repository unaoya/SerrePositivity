module

public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-! # 加群の写像錐の座標と自然性

## 概要

加群の写像錐 `mappingCone φ` の各項を包含と射影で直積として表し（`moduleConeDegreeEquiv`・`mappingConeTermProdIso`）、微分を座標で書く。可換正方形が誘導する錐の写像 `cochainConeArrowMap` を包含・射影で計算し、係数の加法的な変更や錐の三角形の成分との両立を示す。

## 方針

Mathlib の `CochainComplex.mappingCone` の `inl`・`inr`・`fst`・`snd` だけを使い、選んだ直和の実装には依存しない。

## 規約

写像錐は Mathlib のものだけを使う。

## 使われ方

Koszul 複体の錐、線形双対、HomologicalAlgebra/Complex/ConeLES、PerfectComplex。
-/

@[expose] public noncomputable section

universe u

section CochainConeArrowMapPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex CochainComplex

variable {C : Type*} [Category* C] [Preadditive C]
  {P Q P' Q' : CochainComplex C ℤ} (f : P ⟶ Q) (g : P' ⟶ Q')
  [HasHomotopyCofiber f] [HasHomotopyCofiber g]
  (α : Arrow.mk f ⟶ Arrow.mk g)

abbrev cochainConeArrowMap : mappingCone f ⟶ mappingCone g :=
  homotopyCofiber.mapArrowHom f g (fun j => ⟨j - 1, by simp⟩) α

@[reassoc (attr := simp)]
lemma cochainConeArrowMap_inr (n : ℤ) :
    (mappingCone.inr f).f n ≫ (cochainConeArrowMap f g α).f n =
      α.right.f n ≫ (mappingCone.inr g).f n := by
  simp [cochainConeArrowMap, homotopyCofiber.mapArrowHom, mappingCone.inr]

@[reassoc (attr := simp)]
lemma cochainConeArrowMap_inl (n : ℤ) :
    (mappingCone.inl f).v (n + 1) n (by omega) ≫ (cochainConeArrowMap f g α).f n =
      α.left.f (n + 1) ≫ (mappingCone.inl g).v (n + 1) n (by omega) := by
  simp [cochainConeArrowMap, homotopyCofiber.mapArrowHom, mappingCone.inl,
    homotopyCofiber.inrCompHomotopy_hom]

@[reassoc (attr := simp)]
lemma cochainConeArrowMap_fst (n : ℤ) :
    (cochainConeArrowMap f g α).f n ≫ (mappingCone.fst g).1.v n (n + 1) rfl =
      (mappingCone.fst f).1.v n (n + 1) rfl ≫ α.left.f (n + 1) := by
  apply mappingCone.ext_from f (n + 1) n (by omega)
  · simp [cochainConeArrowMap_inl_assoc]
  · simp [cochainConeArrowMap_inr_assoc]

@[reassoc (attr := simp)]
lemma cochainConeArrowMap_snd (n : ℤ) :
    (cochainConeArrowMap f g α).f n ≫ (mappingCone.snd g).v n n (by omega) =
      (mappingCone.snd f).v n n (by omega) ≫ α.right.f n := by
  apply mappingCone.ext_from f (n + 1) n (by omega)
  · simp [cochainConeArrowMap_inl_assoc]
  · simp [cochainConeArrowMap_inr_assoc]

end SerrePositivity

end CochainConeArrowMapPart

section CochainConeCoordinatesPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits CategoryTheory.Category CategoryTheory.Preadditive
open HomologicalComplex.homotopyCofiber
variable {R : Type u} [CommRing R]
variable {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (φ : P ⟶ Q)
    (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j)

/-- 錐の二つの包含・射影は恒等写像を分解する。 -/
theorem moduleCone_coordinates_total :
    fstX φ i j hij ≫ inlX φ j i hij + sndX φ i ≫ inrX φ i =
      𝟙 ((CochainComplex.mappingCone φ).X i) := by
  apply ext_to_X φ i j hij <;> simp <;> rfl

@[simp] theorem moduleCone_fst_inl_apply (x : P.X j) :
    fstX φ i j hij (inlX φ j i hij x) = x :=
  congrArg (fun g ↦ g.hom x) (inlX_fstX φ j i hij)

@[simp] theorem moduleCone_fst_inr_apply (x : Q.X i) :
    fstX φ i j hij (inrX φ i x) = 0 :=
  congrArg (fun g ↦ g.hom x) (inrX_fstX φ i j hij)

@[simp] theorem moduleCone_snd_inl_apply (x : P.X j) :
    sndX φ i (inlX φ j i hij x) = 0 :=
  congrArg (fun g ↦ g.hom x) (inlX_sndX φ j i hij)

@[simp] theorem moduleCone_snd_inr_apply (x : Q.X i) :
    sndX φ i (inrX φ i x) = x :=
  congrArg (fun g ↦ g.hom x) (inrX_sndX φ i)

/-- 錐の項を、包含・射影を保って二つの項の直積へ同定する。 -/
def moduleConeDegreeEquiv :
    (CochainComplex.mappingCone φ).X i ≃ₗ[R] (P.X j × Q.X i) where
  toLinearMap := (fstX φ i j hij).hom.prod (sndX φ i).hom
  invFun x := inlX φ j i hij x.1 + inrX φ i x.2
  left_inv x := congrArg (fun g ↦ g.hom x) (moduleCone_coordinates_total φ i j hij)
  right_inv x := by
    apply Prod.ext
    · change fstX φ i j hij (inlX φ j i hij x.1 + inrX φ i x.2) = x.1
      simp only [map_add, moduleCone_fst_inl_apply, moduleCone_fst_inr_apply, add_zero]
    · change sndX φ i (inlX φ j i hij x.1 + inrX φ i x.2) = x.2
      simp only [map_add, moduleCone_snd_inl_apply, moduleCone_snd_inr_apply, zero_add]

@[simp] theorem moduleConeDegreeEquiv_fst (x : (CochainComplex.mappingCone φ).X i) :
    (moduleConeDegreeEquiv φ i j hij x).1 = fstX φ i j hij x := rfl

@[simp] theorem moduleConeDegreeEquiv_snd (x : (CochainComplex.mappingCone φ).X i) :
    (moduleConeDegreeEquiv φ i j hij x).2 = sndX φ i x := rfl

/-- 第2成分が零なら第1射影は同型。 -/
def moduleConeFstIso (hQ : IsZero (Q.X i)) :
    (CochainComplex.mappingCone φ).X i ≅ P.X j where
  hom := fstX φ i j hij
  inv := inlX φ j i hij
  hom_inv_id := by
    have hzero : sndX φ i ≫ inrX φ i = 0 := by
      rw [hQ.eq_of_tgt (sndX φ i) 0, zero_comp]
    simpa only [hzero, add_zero] using moduleCone_coordinates_total φ i j hij
  inv_hom_id := inlX_fstX φ j i hij

/-- 第1成分が零なら第2射影は同型。 -/
def moduleConeSndIso (hP : IsZero (P.X j)) :
    (CochainComplex.mappingCone φ).X i ≅ Q.X i where
  hom := sndX φ i
  inv := inrX φ i
  hom_inv_id := by
    have hzero : fstX φ i j hij ≫ inlX φ j i hij = 0 := by
      rw [hP.eq_of_tgt (fstX φ i j hij) 0, zero_comp]
    simpa only [hzero, zero_add] using moduleCone_coordinates_total φ i j hij
  inv_hom_id := inrX_sndX φ i

@[simp] theorem moduleConeFstIso_inv (hQ : IsZero (Q.X i)) :
    (moduleConeFstIso φ i j hij hQ).inv =
      (CochainComplex.mappingCone.inl φ).v j i (by change i + 1 = j at hij; omega) := rfl

@[simp] theorem moduleConeSndIso_inv (hP : IsZero (P.X j)) :
    (moduleConeSndIso φ i j hij hP).inv = (CochainComplex.mappingCone.inr φ).f i := rfl

end SerrePositivity.DerivedCompletion

end CochainConeCoordinatesPart

section CochainConeNaturalityPart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Category
open HomologicalComplex.homotopyCofiber
variable {R : Type u} [CommRing R]
variable {P Q P' Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (φ : P ⟶ Q) (ψ : P' ⟶ Q') (α : Arrow.mk φ ⟶ Arrow.mk ψ)

/-- 可換正方形からの錐の写像は、第1包含について左側の写像を誘導する。 -/
@[reassoc] theorem moduleConeArrowMap_inl (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    inlX φ j i hij ≫ (mapArrowHom φ ψ (fun k ↦ ⟨k - 1, by simp⟩) α).f i =
      α.left.f j ≫ inlX ψ j i hij := by
  have h : i + 1 = j := hij
  subst j
  exact cochainConeArrowMap_inl φ ψ α i

/-- 可換正方形からの錐の写像は、第2包含について右側の写像を誘導する。 -/
@[reassoc] theorem moduleConeArrowMap_inr (i : ℤ) :
    inrX φ i ≫ (mapArrowHom φ ψ (fun k ↦ ⟨k - 1, by simp⟩) α).f i =
      α.right.f i ≫ inrX ψ i := by
  exact cochainConeArrowMap_inr φ ψ α i

/-- 錐の写像の第1射影は、左側の写像の第1成分。 -/
@[reassoc] theorem moduleConeArrowMap_fst (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    (mapArrowHom φ ψ (fun k ↦ ⟨k - 1, by simp⟩) α).f i ≫ fstX ψ i j hij =
      fstX φ i j hij ≫ α.left.f j := by
  have h : i + 1 = j := hij
  subst j
  exact cochainConeArrowMap_fst φ ψ α i

/-- 錐の写像の第2射影は、右側の写像の第2成分。 -/
@[reassoc] theorem moduleConeArrowMap_snd (i : ℤ) :
    (mapArrowHom φ ψ (fun k ↦ ⟨k - 1, by simp⟩) α).f i ≫ sndX ψ i =
      sndX φ i ≫ α.right.f i := by
  exact cochainConeArrowMap_snd φ ψ α i

end SerrePositivity.DerivedCompletion

end CochainConeNaturalityPart

section CochainConeAdditiveNaturalityPart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open HomologicalComplex.homotopyCofiber DerivedCompletion
variable {R S : Type u} [CommRing R] [CommRing S]
variable (H : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [H.Additive]
variable {K L K' L' : CochainComplex (ModuleCat.{u} R) ℤ}
variable (φ : K ⟶ L) (ψ : K' ⟶ L') (α : Arrow.mk φ ⟶ Arrow.mk ψ)

/-- The actual additive cone comparison is natural for all commutative squares. -/
@[reassoc]
lemma cochainConeAdditiveIso_inv_naturality :
    (mapHomologicalComplexObjIso φ H).inv ≫
        (H.mapHomologicalComplex (.up ℤ)).map
          (mapArrowHom φ ψ (fun j => ⟨j - 1, by simp⟩) α) =
      mapArrowHom ((H.mapHomologicalComplex (.up ℤ)).map φ)
        ((H.mapHomologicalComplex (.up ℤ)).map ψ) (fun j => ⟨j - 1, by simp⟩)
        ((H.mapHomologicalComplex (.up ℤ)).mapArrow.map α) ≫
          (mapHomologicalComplexObjIso ψ H).inv := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ext_from_X ((H.mapHomologicalComplex (.up ℤ)).map φ) (q + 1) q rfl
  · change (inlX _ (q + 1) q rfl ≫ (mapHomologicalComplexObjXIso φ H q).inv) ≫
        H.map ((mapArrowHom φ ψ (fun j => ⟨j - 1, by simp⟩) α).f q) = _
    rw [inlX_mapHomologicalComplexObjXIso_inv, ← H.map_comp, moduleConeArrowMap_inl]
    simp only [HomologicalComplex.comp_f, moduleConeArrowMap_inl_assoc, H.map_comp]
    change _ = H.map (α.left.f (q + 1)) ≫
      inlX ((H.mapHomologicalComplex (.up ℤ)).map ψ) (q + 1) q rfl ≫
      (mapHomologicalComplexObjXIso ψ H q).inv
    rw [inlX_mapHomologicalComplexObjXIso_inv]
  · change (inrX _ q ≫ (mapHomologicalComplexObjXIso φ H q).inv) ≫
        H.map ((mapArrowHom φ ψ (fun j => ⟨j - 1, by simp⟩) α).f q) = _
    rw [inrX_mapHomologicalComplexObjXIso_inv, ← H.map_comp, moduleConeArrowMap_inr]
    simp only [HomologicalComplex.comp_f, moduleConeArrowMap_inr_assoc, H.map_comp]
    change _ = H.map (α.right.f q) ≫ inrX ((H.mapHomologicalComplex (.up ℤ)).map ψ) q ≫
      (mapHomologicalComplexObjXIso ψ H q).inv
    rw [inrX_mapHomologicalComplexObjXIso_inv]

/-- The forward cone comparison commutes with the actual induced cone maps. -/
@[reassoc]
lemma cochainConeAdditiveIso_hom_naturality :
    (H.mapHomologicalComplex (.up ℤ)).map
        (mapArrowHom φ ψ (fun j => ⟨j - 1, by simp⟩) α) ≫
          (mapHomologicalComplexObjIso ψ H).hom =
      (mapHomologicalComplexObjIso φ H).hom ≫
        mapArrowHom ((H.mapHomologicalComplex (.up ℤ)).map φ)
          ((H.mapHomologicalComplex (.up ℤ)).map ψ) (fun j => ⟨j - 1, by simp⟩)
          ((H.mapHomologicalComplex (.up ℤ)).mapArrow.map α) := by
  have h := congrArg
    (fun f => (mapHomologicalComplexObjIso φ H).hom ≫ f ≫
      (mapHomologicalComplexObjIso ψ H).hom)
    (cochainConeAdditiveIso_inv_naturality H φ ψ α)
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] using h

end SerrePositivity

end CochainConeAdditiveNaturalityPart

section CochainConeProductPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex.homotopyCofiber
variable {R : Type u} [CommRing R]
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ} (φ : K ⟶ L)

/-- Product coordinates of an ordinary cone term. -/
def mappingConeTermProdIso (q : ℤ) :
    (CochainComplex.mappingCone φ).X q ≅ ModuleCat.of R (K.X (q + 1) × L.X q) :=
  XIsoBiprod φ q (q + 1) rfl ≪≫ ModuleCat.biprodIsoProd _ _

/-- The first product projection is the actual cone projection. -/
lemma mappingConeTermProdIso_fst (q : ℤ) :
    (mappingConeTermProdIso φ q).hom ≫
        ModuleCat.ofHom (LinearMap.fst R (K.X (q + 1)) (L.X q)) =
      fstX φ q (q + 1) rfl := by
  have hb : (ModuleCat.biprodIsoProd (K.X (q + 1)) (L.X q)).hom ≫
      ModuleCat.ofHom (LinearMap.fst R (K.X (q + 1)) (L.X q)) = biprod.fst := by
    apply (cancel_epi (ModuleCat.biprodIsoProd (K.X (q + 1)) (L.X q)).inv).mp
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp,
      ModuleCat.biprodIsoProd_inv_comp_fst]
  dsimp only [mappingConeTermProdIso, Iso.trans_hom]
  rw [Category.assoc, hb]
  rfl

/-- The second product projection is the actual cone projection. -/
lemma mappingConeTermProdIso_snd (q : ℤ) :
    (mappingConeTermProdIso φ q).hom ≫
        ModuleCat.ofHom (LinearMap.snd R (K.X (q + 1)) (L.X q)) = sndX φ q := by
  have hb : (ModuleCat.biprodIsoProd (K.X (q + 1)) (L.X q)).hom ≫
      ModuleCat.ofHom (LinearMap.snd R (K.X (q + 1)) (L.X q)) = biprod.snd := by
    apply (cancel_epi (ModuleCat.biprodIsoProd (K.X (q + 1)) (L.X q)).inv).mp
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp,
      ModuleCat.biprodIsoProd_inv_comp_snd]
  dsimp only [mappingConeTermProdIso, Iso.trans_hom]
  rw [Category.assoc, hb]
  apply ext_from_X φ (q + 1) q rfl
  · simp only [← Category.assoc, inlX_XIsoBiprod_hom, biprod.inl_snd, inlX_sndX]
  · simp only [← Category.assoc, inrX_XIsoBiprod_hom, biprod.inr_snd, inrX_sndX]

/-- First component of the actual cone differential. -/
lemma mappingConeTermProdIso_d_fst (q : ℤ) (x : (CochainComplex.mappingCone φ).X q) :
    ((mappingConeTermProdIso φ (q + 1)).hom
      ((CochainComplex.mappingCone φ).d q (q + 1) x)).1 =
      -(K.d (q + 1) (q + 1 + 1) ((mappingConeTermProdIso φ q).hom x).1) := by
  have h := d_fstX φ q (q + 1) (q + 1 + 1) rfl rfl
  rw [← mappingConeTermProdIso_fst φ (q + 1), ← mappingConeTermProdIso_fst φ q] at h
  exact congrArg (fun f => f.hom x) h

/-- Second component of the actual cone differential, including its cross term. -/
lemma mappingConeTermProdIso_d_snd (q : ℤ) (x : (CochainComplex.mappingCone φ).X q) :
    ((mappingConeTermProdIso φ (q + 1)).hom
      ((CochainComplex.mappingCone φ).d q (q + 1) x)).2 =
      φ.f (q + 1) ((mappingConeTermProdIso φ q).hom x).1 +
        L.d q (q + 1) ((mappingConeTermProdIso φ q).hom x).2 := by
  have h := d_sndX φ q (q + 1) rfl
  rw [← mappingConeTermProdIso_snd φ (q + 1), ← mappingConeTermProdIso_fst φ q,
    ← mappingConeTermProdIso_snd φ q] at h
  exact congrArg (fun f => f.hom x) h

end SerrePositivity

end CochainConeProductPart

section CochainConeTrianglePart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex CochainComplex HomComplex
variable {R : Type u} [CommRing R]
variable {P P' : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ P')

/-- The connecting map of a cone is minus its shifted first projection. -/
lemma coneTriangle_mor₃_f (n : ℤ) :
    (mappingCone.triangle f).mor₃.f n =
      -((mappingCone.fst f : Cochain (mappingCone f) P 1).v n (n + 1) rfl ≫
        (P.shiftFunctorObjXIso 1 n (n + 1) rfl).inv) := by
  apply mappingCone.ext_from f (n + 1) n rfl
  · simp only [mappingCone.inl_v_triangle_mor₃_f, Preadditive.comp_neg,
      mappingCone.inl_v_fst_v_assoc]
  · simp only [mappingCone.inr_f_triangle_mor₃_f, Preadditive.comp_neg,
      mappingCone.inr_f_fst_v_assoc, zero_comp, neg_zero]

end SerrePositivity

end CochainConeTrianglePart
