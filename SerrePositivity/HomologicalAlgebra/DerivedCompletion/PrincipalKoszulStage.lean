module
public import SerrePositivity.HomologicalAlgebra.KoszulOneCoordinates

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.KoszulTower

/-! # 一座標Koszul塔の成分と遷移

単一複体の零成分を除き、次数−1と0を元の環へ同定する。
冪による微分と遷移を、この具体的な成分同型の下で計算する。
-/

@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits CategoryTheory.Category CategoryTheory.Preadditive
open HomologicalComplex.homotopyCofiber
variable (R : Type u) [CommRing R]

/-- 元の環を次数0だけに置く複体。 -/
abbrev principalSingle : CochainComplex (ModuleCat.{u} R) ℤ :=
  Adams.oneKoszulUnit

/-- 一座標Koszul塔の次数−1の成分同型。 -/
def principalKoszulStageNegIso (f : R) (n : ℕ) :
    (powerKoszulTower R (fun _ : Fin 1 ↦ f) n).X (-1) ≅ ModuleCat.of R R :=
  Adams.oneKoszulXNegOneIso (f ^ n)

/-- 一座標Koszul塔の次数0の成分同型。 -/
def principalKoszulStageZeroIso (f : R) (n : ℕ) :
    (powerKoszulTower R (fun _ : Fin 1 ↦ f) n).X 0 ≅ ModuleCat.of R R :=
  Adams.oneKoszulXZeroIso (f ^ n)

/-- 負次数の同型は錐の第1射影。 -/
theorem principalKoszulStageNegIso_hom (f : R) (n : ℕ) :
    (principalKoszulStageNegIso R f n).hom =
      fstX (smulId (f ^ n) (principalSingle R)) (-1) 0 (by decide) ≫
        (HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).hom := rfl

/-- 零次数の同型は錐の第2射影。 -/
theorem principalKoszulStageZeroIso_hom (f : R) (n : ℕ) :
    (principalKoszulStageZeroIso R f n).hom =
      sndX (smulId (f ^ n) (principalSingle R)) 0 ≫
        (HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).hom := by
  rfl

/-- 一座標の微分は、成分同型の下でfのn乗によるスカラー作用。 -/
theorem principalKoszulStage_d (f : R) (n : ℕ) :
    (powerKoszulTower R (fun _ : Fin 1 ↦ f) n).d (-1) 0 ≫
      (principalKoszulStageZeroIso R f n).hom =
    (principalKoszulStageNegIso R f n).hom ≫
      (f ^ n • 𝟙 (ModuleCat.of R R)) := by
  rw [principalKoszulStageZeroIso_hom, principalKoszulStageNegIso_hom]
  change d (smulId (f ^ n) (principalSingle R)) (-1) 0 ≫ _ ≫ _ = _
  rw [← assoc, d_sndX _ (-1) 0 (by decide)]
  simp [principalSingle, smulId]

/-- 負次数の逆同型は錐の第1包含。 -/
theorem principalKoszulStageNegIso_inv (f : R) (n : ℕ) :
    (principalKoszulStageNegIso R f n).inv =
      (HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv ≫
        inlX (smulId (f ^ n) (principalSingle R)) 0 (-1) (by decide) := rfl

/-- 零次数の逆同型は錐の第2包含。 -/
theorem principalKoszulStageZeroIso_inv (f : R) (n : ℕ) :
    (principalKoszulStageZeroIso R f n).inv =
      (HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv ≫
        inrX (smulId (f ^ n) (principalSingle R)) 0 := by
  rfl

/-- 負次数の遷移はf倍である。 -/
theorem principalKoszulStageNeg_transition (f : R) (n : ℕ) :
    (powerKoszulTransition R (fun _ : Fin 1 ↦ f) n).f (-1) ≫
      (principalKoszulStageNegIso R f n).hom =
    (principalKoszulStageNegIso R f (n + 1)).hom ≫
      (f • 𝟙 (ModuleCat.of R R)) := by
  apply (cancel_epi (principalKoszulStageNegIso R f (n + 1)).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  rw [principalKoszulStageNegIso_inv]
  change (HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv ≫
    inlX (smulId (f ^ (n + 1)) (principalSingle R)) 0 (-1) (by decide) ≫
      (mapArrowHom (smulId (f ^ (n + 1)) (principalSingle R))
        (smulId (f ^ n) (principalSingle R)) (fun j ↦ ⟨j - 1, by simp⟩)
        (Arrow.homMk (f • 𝟙 _) (𝟙 _) (by
          simp [smulId, pow_succ, smul_smul, koszulComplex, principalSingle]))).f (-1) ≫
          (principalKoszulStageNegIso R f n).hom = _
  simp [koszulComplex, mapArrowHom, principalSingle,
    Homotopy.trans, Homotopy.ofEq, Homotopy.compLeft,
    inrCompHomotopy_hom, principalKoszulStageNegIso_hom, smulId]

/-- 零次数の遷移は恒等写像である。 -/
theorem principalKoszulStageZero_transition (f : R) (n : ℕ) :
    (powerKoszulTransition R (fun _ : Fin 1 ↦ f) n).f 0 ≫
      (principalKoszulStageZeroIso R f n).hom =
    (principalKoszulStageZeroIso R f (n + 1)).hom := by
  apply (cancel_epi (principalKoszulStageZeroIso R f (n + 1)).inv).mp
  rw [Iso.inv_hom_id, principalKoszulStageZeroIso_inv]
  change (HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv ≫
    inrX (smulId (f ^ (n + 1)) (principalSingle R)) 0 ≫
      (mapArrowHom (smulId (f ^ (n + 1)) (principalSingle R))
        (smulId (f ^ n) (principalSingle R)) (fun j ↦ ⟨j - 1, by simp⟩)
        (Arrow.homMk (f • 𝟙 _) (𝟙 _) (by
          simp [smulId, pow_succ, smul_smul, koszulComplex, principalSingle]))).f 0 ≫
          (principalKoszulStageZeroIso R f n).hom = _
  simp [koszulComplex, mapArrowHom,
    principalKoszulStageZeroIso_hom, principalSingle]

end SerrePositivity.DerivedCompletion
