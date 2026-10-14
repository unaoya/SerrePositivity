module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PairKoszulProduct
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PairTowerUniqueness

/-! # 二座標Koszul完備化の短複体と行列モデルの比較 -/

@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits CategoryTheory.Category
open HomologicalComplex.homotopyCofiber
variable (R : Type u) [CommRing R]

/-- 外側の錐の次数−1を、三つの境界変数へ同定する。 -/
def pairCompletionNegEquiv (f d : R) :
    (pairKoszulCompletionComplex R f d).X (-1) ≃ₗ[R]
      (((ℕ → R) × (ℕ → R)) × (ℕ → R)) :=
  (CochainComplex.shiftFunctorObjXIso _ (-1) (-1) (-2) (by norm_num)).toLinearEquiv ≪≫ₗ
    moduleConeDegreeEquiv (pairKoszulDifference R f d) (-2) (-1) (by decide) ≪≫ₗ
      (pairKoszulProductNegOneEquiv R f d).prodCongr (pairKoszulProductNegTwoEquiv R f d)

/-- 外側の錐の次数0を、サイクルの三つの列へ同定する。 -/
def pairCompletionZeroEquiv (f d : R) :
    (pairKoszulCompletionComplex R f d).X 0 ≃ₗ[R]
      ((ℕ → R) × ((ℕ → R) × (ℕ → R))) :=
  (CochainComplex.shiftFunctorObjXIso _ (-1) 0 (-1) (by norm_num)).toLinearEquiv ≪≫ₗ
    moduleConeDegreeEquiv (pairKoszulDifference R f d) (-1) 0 (by decide) ≪≫ₗ
      (pairKoszulProductZeroEquiv R f d).prodCongr (pairKoszulProductNegOneEquiv R f d) ≪≫ₗ
        (LinearEquiv.refl R (ℕ → R)).prodCongr (LinearEquiv.neg R)

/-- 外側の錐の次数1を、サイクルの障害となる列へ同定する。 -/
def pairCompletionOneEquiv (f d : R) :
    (pairKoszulCompletionComplex R f d).X 1 ≃ₗ[R] (ℕ → R) :=
  (CochainComplex.shiftFunctorObjXIso _ (-1) 1 0 (by norm_num)).toLinearEquiv ≪≫ₗ
    (moduleConeSndIso (pairKoszulDifference R f d) 0 1 rfl
      (pairKoszulProduct_isZero R f d 1 (Or.inr (by norm_num)))).toLinearEquiv ≪≫ₗ
        pairKoszulProductZeroEquiv R f d ≪≫ₗ LinearEquiv.neg R

@[simp] theorem pairCompletionNegEquiv_fst (f d : R)
    (x : (pairKoszulCompletionComplex R f d).X (-1)) :
    (pairCompletionNegEquiv R f d x).1 = pairKoszulProductNegOneEquiv R f d
      (fstX (pairKoszulDifference R f d) (-2) (-1) (by decide) x) := rfl

@[simp] theorem pairCompletionNegEquiv_snd (f d : R)
    (x : (pairKoszulCompletionComplex R f d).X (-1)) :
    (pairCompletionNegEquiv R f d x).2 = pairKoszulProductNegTwoEquiv R f d
      (sndX (pairKoszulDifference R f d) (-2) x) := rfl

@[simp] theorem pairCompletionZeroEquiv_fst (f d : R)
    (x : (pairKoszulCompletionComplex R f d).X 0) :
    (pairCompletionZeroEquiv R f d x).1 = pairKoszulProductZeroEquiv R f d
      (fstX (pairKoszulDifference R f d) (-1) 0 (by decide) x) := rfl

@[simp] theorem pairCompletionZeroEquiv_snd (f d : R)
    (x : (pairKoszulCompletionComplex R f d).X 0) :
    (pairCompletionZeroEquiv R f d x).2 = -pairKoszulProductNegOneEquiv R f d
      (sndX (pairKoszulDifference R f d) (-1) x) := rfl

@[simp] theorem pairCompletionOneEquiv_apply (f d : R)
    (x : (pairKoszulCompletionComplex R f d).X 1) :
    pairCompletionOneEquiv R f d x = -pairKoszulProductZeroEquiv R f d
      (sndX (pairKoszulDifference R f d) 0 x) := rfl

/-- 一段シフトした微分の負号。 -/
theorem pairCompletion_d_eq (f d : R) (i j : ℤ) :
    (pairKoszulCompletionComplex R f d).d i j =
      -HomologicalComplex.homotopyCofiber.d (pairKoszulDifference R f d) (i + -1) (j + -1) := by
  change (-1 : ℤ).negOnePow • _ = -_
  simp
  rfl

/-- 最低次数からの微分は、交差変数を含む行列モデルの境界。 -/
theorem pairCompletion_d_neg (f d : R)
    (x : (pairKoszulCompletionComplex R f d).X (-1)) :
    pairCompletionZeroEquiv R f d ((pairKoszulCompletionComplex R f d).d (-1) 0 x) =
      pairTowerBoundaryTriple R f d (pairCompletionNegEquiv R f d x) := by
  apply Prod.ext
  · rw [pairCompletionZeroEquiv_fst]
    have h := congrArg (fun g ↦ g.hom x)
      (d_fstX (pairKoszulDifference R f d) (-2) (-1) 0 (by decide) (by decide))
    rw [pairCompletion_d_eq]
    change pairKoszulProductZeroEquiv R f d
      (fstX (pairKoszulDifference R f d) (-1) 0 (by decide)
        (-HomologicalComplex.homotopyCofiber.d (pairKoszulDifference R f d) (-2) (-1) x)) = _
    rw [map_neg, map_neg]
    change fstX (pairKoszulDifference R f d) (-1) 0 (by decide)
      (HomologicalComplex.homotopyCofiber.d (pairKoszulDifference R f d) (-2) (-1) x) =
        -(pairKoszulProduct R f d).d (-1) 0
          (fstX (pairKoszulDifference R f d) (-2) (-1) (by decide) x) at h
    rw [h, map_neg, neg_neg, pairKoszulProduct_d_negOne]
    rfl
  · rw [pairCompletionZeroEquiv_snd]
    have h := congrArg (fun g : (CochainComplex.mappingCone (pairKoszulDifference R f d)).X (-2) ⟶
        (pairKoszulProduct R f d).X (-1) ↦ g.hom x)
      (d_sndX (pairKoszulDifference R f d) (-2) (-1) (by decide))
    rw [pairCompletion_d_eq]
    change -pairKoszulProductNegOneEquiv R f d
      (sndX (pairKoszulDifference R f d) (-1)
        (-HomologicalComplex.homotopyCofiber.d (pairKoszulDifference R f d) (-2) (-1) x)) = _
    rw [map_neg, map_neg, neg_neg]
    change sndX (pairKoszulDifference R f d) (-1)
      (HomologicalComplex.homotopyCofiber.d (pairKoszulDifference R f d) (-2) (-1) x) =
        (pairKoszulDifference R f d).f (-1)
          (fstX (pairKoszulDifference R f d) (-2) (-1) (by decide) x) +
        (pairKoszulProduct R f d).d (-2) (-1)
          (sndX (pairKoszulDifference R f d) (-2) x) at h
    rw [h, map_add, pairKoszulProductNegOne_difference, pairKoszulProduct_d_negTwo]
    simp [pairTowerBoundaryTriple, pairCompletionNegEquiv_fst, pairCompletionNegEquiv_snd,
      sub_eq_add_neg]

/-- 零次数からの微分は、行列モデルのサイクル条件。 -/
theorem pairCompletion_d_zero (f d : R)
    (x : (pairKoszulCompletionComplex R f d).X 0) :
    pairCompletionOneEquiv R f d ((pairKoszulCompletionComplex R f d).d 0 1 x) =
      pairTowerObstruction R f d (pairCompletionZeroEquiv R f d x) := by
  rw [pairCompletionOneEquiv_apply, pairCompletion_d_eq]
  change -pairKoszulProductZeroEquiv R f d
    (sndX (pairKoszulDifference R f d) 0
      (-HomologicalComplex.homotopyCofiber.d (pairKoszulDifference R f d) (-1) 0 x)) = _
  rw [map_neg, map_neg, neg_neg]
  have h := congrArg (fun g : (CochainComplex.mappingCone (pairKoszulDifference R f d)).X (-1) ⟶
      (pairKoszulProduct R f d).X 0 ↦ g.hom x)
    (d_sndX (pairKoszulDifference R f d) (-1) 0 (by decide))
  change sndX (pairKoszulDifference R f d) 0
    (HomologicalComplex.homotopyCofiber.d (pairKoszulDifference R f d) (-1) 0 x) =
      (pairKoszulDifference R f d).f 0
        (fstX (pairKoszulDifference R f d) (-1) 0 (by decide) x) +
      (pairKoszulProduct R f d).d (-1) 0
        (sndX (pairKoszulDifference R f d) (-1) x) at h
  rw [h, map_add, pairKoszulProductZero_difference, pairKoszulProduct_d_negOne]
  simp [pairTowerObstruction, pairCompletionZeroEquiv_fst, pairCompletionZeroEquiv_snd,
    sub_neg_eq_add, add_assoc]

/-- 具体的な二座標完備化の短複体と、交差境界を保持した行列モデルの同型。 -/
def pairCompletionShortComplexIso (f d : R) :
    (pairKoszulCompletionComplex R f d).sc 0 ≅ pairTowerShortComplex R f d :=
  (pairKoszulCompletionComplex R f d).isoSc' (-1) 0 1
    ((ComplexShape.up ℤ).prev_eq' (show (ComplexShape.up ℤ).Rel (-1) 0 by decide))
    ((ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel 0 1 from rfl)) ≪≫
      ShortComplex.isoMk (pairCompletionNegEquiv R f d).toModuleIso
        (pairCompletionZeroEquiv R f d).toModuleIso (pairCompletionOneEquiv R f d).toModuleIso
        (by apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
            exact (pairCompletion_d_neg R f d x).symm)
        (by apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
            exact (pairCompletion_d_zero R f d x).symm)

/-- 元の二座標Koszul完備化の短複体から、行列モデルへの同型。 -/
def pairKoszulCompletionShortComplexIso (f d : R) :
    (koszulCompletionComplex R (pairKoszulCoordinates R f d)).sc 0 ≅
      pairTowerShortComplex R f d :=
  (HomologicalComplex.shortComplexFunctor _ _ 0).mapIso (pairKoszulCompletionIso R f d) ≪≫
    pairCompletionShortComplexIso R f d

/-- 元の二座標Koszul完備化の実際のH⁰から、行列モデルのH⁰への同型。 -/
def pairKoszulCompletionH0Equiv (f d : R) :
    (koszulCompletionComplex R (pairKoszulCoordinates R f d)).homology 0 ≃ₗ[R]
      (pairTowerShortComplex R f d).homology :=
  (ShortComplex.homologyMapIso (pairKoszulCompletionShortComplexIso R f d)).toLinearEquiv

end SerrePositivity.DerivedCompletion
