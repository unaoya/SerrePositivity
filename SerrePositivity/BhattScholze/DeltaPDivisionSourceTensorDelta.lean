module

public import SerrePositivity.BhattScholze.DeltaPDivisionSourceTensor

/-! # 実通常テンソルのδ構造と両因子の標準包含

raw包のδ切断を標準比較同型とW₂写像で引き戻す。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (y : A)
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "R₀" => TensorProduct P₀ A P₀
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "B₀" => DeltaAdjoinDivision D (p : A) a₀

/-- 実通常テンソル上の、raw包の標準比較で引き戻した具体的δ構造。 -/
def deltaPDivisionSourceTensorDelta :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    DeltaStructure p R₀ := by
  letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  letI : Module P₀ P₀ := Algebra.toModule
  let e := deltaPDivisionSourceTensorEquiv (σ := σ) D y
  let E := deltaAdjoinDivisionStructure D (p : A) a₀
  exact
    { sectionHom := (wittTwoMap e.symm.toRingHom).comp (E.sectionHom.comp e.toRingHom)
      coeff_zero := by
        intro r
        simp only [RingHom.comp_apply, wittTwoMap_coeff, E.coeff_zero]
        exact e.symm_apply_apply r }

/-- 実通常テンソルからraw包への標準環同型はδ構造を保存する。 -/
theorem deltaPDivisionSourceTensorEquiv_isDeltaHom :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    (deltaPDivisionSourceTensorDelta (σ := σ) D y).IsDeltaHom
      (deltaAdjoinDivisionStructure D (p : A) a₀)
      (deltaPDivisionSourceTensorEquiv D y).toRingHom := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  let e := deltaPDivisionSourceTensorEquiv (σ := σ) D y
  let E := deltaAdjoinDivisionStructure D (p : A) a₀
  intro r
  change e ((wittTwoMap e.symm.toRingHom (E.sectionHom (e r))).coeff 1) = E.delta (e r)
  rw [wittTwoMap_coeff]
  exact e.apply_symm_apply _

/-- raw包から実通常テンソルへの標準逆同型もδ構造を保存する。 -/
theorem deltaPDivisionSourceTensorEquiv_symm_isDeltaHom :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    (deltaAdjoinDivisionStructure D (p : A) a₀).IsDeltaHom
      (deltaPDivisionSourceTensorDelta (σ := σ) D y)
      (deltaPDivisionSourceTensorEquiv D y).symm.toRingHom := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  let e := deltaPDivisionSourceTensorEquiv (σ := σ) D y
  intro r
  apply e.injective
  change e (e.symm ((deltaAdjoinDivisionStructure D (p : A) a₀).delta r)) =
    e ((deltaPDivisionSourceTensorDelta (σ := σ) D y).delta (e.symm r))
  rw [RingEquiv.apply_symm_apply]
  have h := deltaPDivisionSourceTensorEquiv_isDeltaHom (σ := σ) D y (e.symm r)
  change e ((deltaPDivisionSourceTensorDelta (σ := σ) D y).delta (e.symm r)) =
    (deltaAdjoinDivisionStructure D (p : A) a₀).delta (e (e.symm r)) at h
  rw [RingEquiv.apply_symm_apply] at h
  exact h.symm

/-- 通常テンソルの元の基底Aの標準包含はδ射。 -/
theorem deltaPDivisionSourceTensor_includeLeft_isDeltaHom :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    D.IsDeltaHom (deltaPDivisionSourceTensorDelta (σ := σ) D y)
      Algebra.TensorProduct.includeLeftRingHom := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  have h := (deltaPDivisionSourceTensorEquiv_symm_isDeltaHom (σ := σ) D y).comp
    (deltaAdjoinDivisionMap_isDeltaHom D (p : A) a₀)
  change D.IsDeltaHom (deltaPDivisionSourceTensorDelta (σ := σ) D y)
    ((deltaPDivisionSourceRawToTensor D y).comp (deltaAdjoinDivisionMap D (p : A) a₀)) at h
  rw [deltaPDivisionSourceRawToTensor_comp_base] at h
  exact h

/-- 通常テンソルの終域自由δ環Lの標準包含もδ射。 -/
theorem deltaPDivisionSourceTensor_includeRight_isDeltaHom :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    (relativeFreeDeltaStructure σ D).IsDeltaHom (deltaPDivisionSourceTensorDelta (σ := σ) D y)
      Algebra.TensorProduct.includeRight.toRingHom := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  let E := relativeFreeDeltaStructure σ D
  let J := E.deltaClosure (deltaDivisionRelationIdeal (p : A) a₀)
  have hq := E.isDeltaHom_quotient_mk J (E.isStable_deltaClosure _)
  have h := (deltaPDivisionSourceTensorEquiv_symm_isDeltaHom (σ := σ) D y).comp hq
  change E.IsDeltaHom (deltaPDivisionSourceTensorDelta (σ := σ) D y)
    ((deltaPDivisionSourceRawToTensor D y).comp (Ideal.Quotient.mk J)) at h
  rw [deltaPDivisionSourceRawToTensor_comp_quotient] at h
  exact h

/-- 両因子の標準包含をδ射にするδ構造は、構成したものに一意に一致する。 -/
theorem deltaPDivisionSourceTensorDelta_unique :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    ∀ E : DeltaStructure p R₀,
      D.IsDeltaHom E Algebra.TensorProduct.includeLeftRingHom →
      (relativeFreeDeltaStructure σ D).IsDeltaHom E Algebra.TensorProduct.includeRight.toRingHom →
      E = deltaPDivisionSourceTensorDelta (σ := σ) D y := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  intro E hL hR
  let T := deltaPDivisionSourceTensorDelta (σ := σ) D y
  have hL' := deltaPDivisionSourceTensor_includeLeft_isDeltaHom (σ := σ) D y
  have hR' := deltaPDivisionSourceTensor_includeRight_isDeltaHom (σ := σ) D y
  have hLeft : E.sectionHom.comp Algebra.TensorProduct.includeLeftRingHom =
      T.sectionHom.comp Algebra.TensorProduct.includeLeftRingHom :=
    ((D.isDeltaHom_iff_sectionHom_comp E _).mp hL).symm.trans
      ((D.isDeltaHom_iff_sectionHom_comp T _).mp hL')
  have hRight : E.sectionHom.comp Algebra.TensorProduct.includeRight.toRingHom =
      T.sectionHom.comp Algebra.TensorProduct.includeRight.toRingHom :=
    (((relativeFreeDeltaStructure σ D).isDeltaHom_iff_sectionHom_comp E _).mp hR).symm.trans
      (((relativeFreeDeltaStructure σ D).isDeltaHom_iff_sectionHom_comp T _).mp hR')
  have hs : E.sectionHom = T.sectionHom := Algebra.TensorProduct.ringHom_ext hLeft hRight
  apply DeltaStructure.ext
  intro r
  exact congrArg (fun z : WittTwo p R₀ => z.coeff 1) (RingHom.congr_fun hs r)

end SerrePositivity.BhattScholze
