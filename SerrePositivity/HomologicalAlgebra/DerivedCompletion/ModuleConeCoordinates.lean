module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerComplex
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-! # 加群のmapping coneの項の具体的な座標

錐の包含と射影から項の直積表示を作る。選択された直和の実装に依存しない。
-/

@[expose] public noncomputable section
universe u
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

end SerrePositivity.DerivedCompletion
