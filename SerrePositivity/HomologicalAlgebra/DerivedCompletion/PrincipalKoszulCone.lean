module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerComplex
public import SerrePositivity.HomologicalAlgebra.CochainConeCoordinates
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalKoszulProduct

/-! # 一座標のKoszul完備化複体の三項座標

外側の錐を一段シフトした複体の成分を列で表す。
次数0の第2成分と次数1の符号を反転して、三項モデルの符号へ合わせる。
-/

@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits CategoryTheory.Category
open HomologicalComplex.homotopyCofiber
variable (R : Type u) [CommRing R]

/-- 一座標Koszul塔の実際の直積。 -/
abbrev principalKoszulProduct (f : R) := piObj (powerKoszulTower R (fun _ : Fin 1 ↦ f))
/-- 一座標Koszul塔の実際の差分写像。 -/
abbrev principalKoszulDifference (f : R) := complexTowerDifference R
  (powerKoszulTower R (fun _ : Fin 1 ↦ f)) (powerKoszulTransition R (fun _ : Fin 1 ↦ f))

/-- 実際の完備化複体の次数−1を列へ同定する。 -/
def principalCompletionNegEquiv (f : R) :
    (koszulCompletionComplex R (fun _ : Fin 1 ↦ f)).X (-1) ≃ₗ[R] (ℕ → R) :=
  (CochainComplex.shiftFunctorObjXIso _ (-1) (-1) (-2) (by norm_num)).toLinearEquiv.trans
    ((moduleConeFstIso (principalKoszulDifference R f) (-2) (-1) (by decide)
      (principalKoszulProduct_isZero R f (-2) (Or.inl (by norm_num)))).toLinearEquiv.trans
        (principalKoszulProductNegEquiv R f))

/-- 実際の完備化複体の次数0を列の組へ同定する。 -/
def principalCompletionZeroEquiv (f : R) :
    (koszulCompletionComplex R (fun _ : Fin 1 ↦ f)).X 0 ≃ₗ[R] ((ℕ → R) × (ℕ → R)) :=
  (CochainComplex.shiftFunctorObjXIso _ (-1) 0 (-1) (by norm_num)).toLinearEquiv ≪≫ₗ
    moduleConeDegreeEquiv (principalKoszulDifference R f) (-1) 0 (by decide) ≪≫ₗ
      (principalKoszulProductZeroEquiv R f).prodCongr
        (principalKoszulProductNegEquiv R f) ≪≫ₗ
          (LinearEquiv.refl R (ℕ → R)).prodCongr (LinearEquiv.neg R)

/-- 実際の完備化複体の次数1を列へ同定する。 -/
def principalCompletionOneEquiv (f : R) :
    (koszulCompletionComplex R (fun _ : Fin 1 ↦ f)).X 1 ≃ₗ[R] (ℕ → R) :=
  (CochainComplex.shiftFunctorObjXIso _ (-1) 1 0 (by norm_num)).toLinearEquiv ≪≫ₗ
    (moduleConeSndIso (principalKoszulDifference R f) 0 1 rfl
      (principalKoszulProduct_isZero R f 1 (Or.inr (by norm_num)))).toLinearEquiv ≪≫ₗ
        principalKoszulProductZeroEquiv R f ≪≫ₗ LinearEquiv.neg R

@[simp] theorem principalCompletionNegEquiv_apply (f : R)
    (x : (koszulCompletionComplex R (fun _ : Fin 1 ↦ f)).X (-1)) :
    principalCompletionNegEquiv R f x = principalKoszulProductNegEquiv R f
      (fstX (principalKoszulDifference R f) (-2) (-1) (by decide) x) := rfl

@[simp] theorem principalCompletionZeroEquiv_fst (f : R)
    (x : (koszulCompletionComplex R (fun _ : Fin 1 ↦ f)).X 0) :
    (principalCompletionZeroEquiv R f x).1 = principalKoszulProductZeroEquiv R f
      (fstX (principalKoszulDifference R f) (-1) 0 (by decide) x) := rfl

@[simp] theorem principalCompletionZeroEquiv_snd (f : R)
    (x : (koszulCompletionComplex R (fun _ : Fin 1 ↦ f)).X 0) :
    (principalCompletionZeroEquiv R f x).2 = -principalKoszulProductNegEquiv R f
      (sndX (principalKoszulDifference R f) (-1) x) := rfl

@[simp] theorem principalCompletionOneEquiv_apply (f : R)
    (x : (koszulCompletionComplex R (fun _ : Fin 1 ↦ f)).X 1) :
    principalCompletionOneEquiv R f x = -principalKoszulProductZeroEquiv R f
      (sndX (principalKoszulDifference R f) 0 x) := rfl

/-- 一段シフトした実際の微分の符号。 -/
theorem principalCompletion_d_eq (f : R) (i j : ℤ) :
    (koszulCompletionComplex R (fun _ : Fin 1 ↦ f)).d i j =
      -d (principalKoszulDifference R f) (i + -1) (j + -1) := by
  change (-1 : ℤ).negOnePow • _ = -_
  simp
  rfl

/-- 次数−1から0への微分は、具体的三項モデルの境界写像。 -/
theorem principalCompletion_d_neg (f : R)
    (x : (koszulCompletionComplex R (fun _ : Fin 1 ↦ f)).X (-1)) :
    principalCompletionZeroEquiv R f
      ((koszulCompletionComplex R (fun _ : Fin 1 ↦ f)).d (-1) 0 x) =
    principalTowerBoundaryPair R f (principalCompletionNegEquiv R f x) := by
  apply Prod.ext
  · rw [principalCompletionZeroEquiv_fst, principalCompletionNegEquiv_apply]
    have h := congrArg (fun g ↦ g.hom x)
      (d_fstX (principalKoszulDifference R f) (-2) (-1) 0 (by decide) (by decide))
    rw [principalCompletion_d_eq]
    change principalKoszulProductZeroEquiv R f
      (fstX (principalKoszulDifference R f) (-1) 0 (by decide)
        (-d (principalKoszulDifference R f) (-2) (-1) x)) = _
    rw [map_neg, map_neg]
    change -principalKoszulProductZeroEquiv R f
      (fstX (principalKoszulDifference R f) (-1) 0 (by decide)
        (d (principalKoszulDifference R f) (-2) (-1) x)) = _
    change fstX (principalKoszulDifference R f) (-1) 0 (by decide)
      (d (principalKoszulDifference R f) (-2) (-1) x) =
        -(principalKoszulProduct R f).d (-1) 0
          (fstX (principalKoszulDifference R f) (-2) (-1) (by decide) x) at h
    rw [h, map_neg, neg_neg, principalKoszulProduct_d]
    rfl
  · rw [principalCompletionZeroEquiv_snd, principalCompletionNegEquiv_apply]
    have h := congrArg (fun g ↦ g.hom x)
      (d_sndX (principalKoszulDifference R f) (-2) (-1) (by decide))
    have hz : sndX (principalKoszulDifference R f) (-2) x = 0 :=
      (ModuleCat.isZero_iff_subsingleton.mp
        (principalKoszulProduct_isZero R f (-2) (Or.inl (by norm_num)))).elim _ _
    rw [principalCompletion_d_eq]
    change -principalKoszulProductNegEquiv R f
      (sndX (principalKoszulDifference R f) (-1)
        (-d (principalKoszulDifference R f) (-2) (-1) x)) = _
    rw [map_neg, map_neg, neg_neg]
    change sndX (principalKoszulDifference R f) (-1)
      (d (principalKoszulDifference R f) (-2) (-1) x) =
        (principalKoszulDifference R f).f (-1)
          (fstX (principalKoszulDifference R f) (-2) (-1) (by decide) x) +
            (principalKoszulProduct R f).d (-2) (-1)
              (sndX (principalKoszulDifference R f) (-2) x) at h
    rw [hz, map_zero, add_zero] at h
    rw [h, principalKoszulProductNeg_difference]
    rfl

/-- 次数0から1への微分は、具体的三項モデルのサイクル条件。 -/
theorem principalCompletion_d_zero (f : R)
    (x : (koszulCompletionComplex R (fun _ : Fin 1 ↦ f)).X 0) :
    principalCompletionOneEquiv R f
      ((koszulCompletionComplex R (fun _ : Fin 1 ↦ f)).d 0 1 x) =
    principalTowerObstruction R f (principalCompletionZeroEquiv R f x) := by
  rw [principalCompletionOneEquiv_apply]
  rw [principalCompletion_d_eq]
  change -principalKoszulProductZeroEquiv R f
    (sndX (principalKoszulDifference R f) 0
      (-d (principalKoszulDifference R f) (-1) 0 x)) = _
  rw [map_neg, map_neg, neg_neg]
  have h := congrArg (fun g : (CochainComplex.mappingCone
    (principalKoszulDifference R f)).X (-1) ⟶ (principalKoszulProduct R f).X 0 ↦ g.hom x)
    (d_sndX (principalKoszulDifference R f) (-1) 0 (by decide))
  change sndX (principalKoszulDifference R f) 0
    (d (principalKoszulDifference R f) (-1) 0 x) =
      (principalKoszulDifference R f).f 0
        (fstX (principalKoszulDifference R f) (-1) 0 (by decide) x) +
          (principalKoszulProduct R f).d (-1) 0
            (sndX (principalKoszulDifference R f) (-1) x) at h
  rw [h, map_add, principalKoszulProductZero_difference, principalKoszulProduct_d]
  simp [principalTowerObstruction, principalCompletionZeroEquiv_fst,
    principalCompletionZeroEquiv_snd, sub_neg_eq_add]

/-- 実際のKoszul完備化の短複体と、具体的な三項モデルの同型。 -/
def principalCompletionShortComplexIso (f : R) :
    (koszulCompletionComplex R (fun _ : Fin 1 ↦ f)).sc 0 ≅
      principalTowerShortComplex R f :=
  (koszulCompletionComplex R (fun _ : Fin 1 ↦ f)).isoSc' (-1) 0 1
    ((ComplexShape.up ℤ).prev_eq' (show (ComplexShape.up ℤ).Rel (-1) 0 by decide))
    ((ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel 0 1 from rfl)) ≪≫
      ShortComplex.isoMk (principalCompletionNegEquiv R f).toModuleIso
        (principalCompletionZeroEquiv R f).toModuleIso
        (principalCompletionOneEquiv R f).toModuleIso
        (by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          exact (principalCompletion_d_neg R f x).symm)
        (by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          exact (principalCompletion_d_zero R f x).symm)

/-- 実際のKoszul完備化のH⁰を、一座標の反射加群へ同定する。 -/
def principalCompletionH0Equiv (f : R) :
    (koszulCompletionComplex R (fun _ : Fin 1 ↦ f)).homology 0 ≃ₗ[R]
      PrincipalReflectionModule R f :=
  (ShortComplex.homologyMapIso (principalCompletionShortComplexIso R f)).toLinearEquiv.trans
    (principalTowerHomologyEquiv R f)

end SerrePositivity.DerivedCompletion
