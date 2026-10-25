module

public import SerrePositivity.BhattScholze.RootedExtension.Division.DeltaPDivisionSourceTensorRegular
public import SerrePositivity.BhattScholze.Delta.Division.DeltaDivisionPDCompletion

/-! # 実通常テンソル入力と既存δ除算候補の実導来完備化H⁰比較

同型な通常入力環を、既存の環としての完備化普遍性で比較する。
G7・原典の導来δpushout比較・古典的完備化への置換は用いない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
variable (hpA : Function.Injective (fun x : A => (p : A) * x))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (v : Aˣ) (hv : (v : A) = D.delta (p : A))
variable (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "R₀" => TensorProduct P₀ A P₀
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "U₀" => DeltaDivisionTorsionQuotient D (p : A) a₀
local notation "d₀" => deltaDivisionTorsionMap D (p : A) a₀ (p : A)
local notation "C₀" => DerivedDeltaDivisionCompletion D (p : A) a₀
local notation "H₀" => PDCompletionH0 R₀ p (p : R₀)
include hpA hg hv hy

/-- 実通常テンソルの(p,p)導来完備化H⁰と既存候補は、標準単位を保つ環同型で一意に比較できる。 -/
theorem existsUnique_deltaPDivisionSourceTensorCompletionEquiv :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    letI := pdCompletionCommRing R₀ p (p : R₀)
    letI := derivedDeltaDivisionCommRing D (p : A) a₀
    ∃! e : H₀ ≃+* C₀,
      e.toRingHom.comp (pdCompletionUnit R₀ p (p : R₀)) =
        (pdCompletionUnit U₀ p d₀).comp
          (deltaPDivisionSourceTensorTorsionEquiv D y hpA hg v hv hy).toRingHom := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  let := pdCompletionCommRing R₀ p (p : R₀)
  let := derivedDeltaDivisionCommRing D (p : A) a₀
  let E := deltaPDivisionSourceTensorTorsionEquiv D y hpA hg v hv hy
  let jH := pdCompletionUnit R₀ p (p : R₀)
  let jC := pdCompletionUnit U₀ p d₀
  let f₀ := jC.comp E.toRingHom
  let g₀ := jH.comp E.symm.toRingHom
  have hpH := pdCompletionH0_self_complete_p R₀ p (p : R₀)
  have hdH := pdCompletionH0_self_complete_d R₀ p (p : R₀)
  have hpC := pdCompletionH0_self_complete_p U₀ p d₀
  have hdC := pdCompletionH0_self_complete_d U₀ p d₀
  have hfd : IsModuleComplete C₀ (f₀ (p : R₀)) (ModuleCat.of C₀ C₀) := by
    simpa only [map_natCast] using hpC
  have hdU : d₀ = (p : U₀) := map_natCast (deltaDivisionTorsionMap D (p : A) a₀) p
  have hgNat : g₀ d₀ = (p : H₀) := (congrArg g₀ hdU).trans (map_natCast g₀ p)
  have hgd : IsModuleComplete H₀ (g₀ d₀) (ModuleCat.of H₀ H₀) := by
    simpa only [hgNat] using hpH
  obtain ⟨f, hf, hfu⟩ := existsUnique_pdCompletionRingHom R₀ p (p : R₀) C₀ f₀ hpC hfd
  obtain ⟨g, hG, _⟩ := existsUnique_pdCompletionRingHom U₀ p d₀ H₀ g₀ hpH hgd
  have hfg : f.comp g = RingHom.id C₀ := by
    apply pdCompletionRingHom_ext U₀ p d₀ C₀ jC hpC hdC
    · rw [RingHom.comp_assoc, hG, ← RingHom.comp_assoc, hf]
      apply RingHom.ext
      intro r
      change jC (E (E.symm r)) = jC r
      rw [RingEquiv.apply_symm_apply]
    · exact RingHom.id_comp jC
  have hgf : g.comp f = RingHom.id H₀ := by
    apply pdCompletionRingHom_ext R₀ p (p : R₀) H₀ jH hpH hdH
    · rw [RingHom.comp_assoc, hf, ← RingHom.comp_assoc, hG]
      apply RingHom.ext
      intro r
      change jH (E.symm (E r)) = jH r
      rw [RingEquiv.symm_apply_apply]
    · exact RingHom.id_comp jH
  let e := RingEquiv.ofRingHom f g hfg hgf
  refine ⟨e, hf, ?_⟩
  intro e' he'
  apply RingEquiv.ext
  intro r
  exact RingHom.congr_fun (hfu e'.toRingHom he') r

/-- 標準単位で正規化した、実通常テンソルの実完備化H⁰と既存δ除算候補の環同型。 -/
def deltaPDivisionSourceTensorCompletionEquiv :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    letI := pdCompletionCommRing R₀ p (p : R₀)
    letI := derivedDeltaDivisionCommRing D (p : A) a₀
    H₀ ≃+* C₀ := by
  letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  letI : Module P₀ P₀ := Algebra.toModule
  letI := pdCompletionCommRing R₀ p (p : R₀)
  letI := derivedDeltaDivisionCommRing D (p : A) a₀
  exact Classical.choose (existsUnique_deltaPDivisionSourceTensorCompletionEquiv D y hpA hg v hv hy)

/-- 実完備化比較は、元の通常入力環の標準単位を保つ。 -/
theorem deltaPDivisionSourceTensorCompletionEquiv_comp_unit :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    letI := pdCompletionCommRing R₀ p (p : R₀)
    letI := derivedDeltaDivisionCommRing D (p : A) a₀
    (deltaPDivisionSourceTensorCompletionEquiv D y hpA hg v hv hy).toRingHom.comp
      (pdCompletionUnit R₀ p (p : R₀)) =
        (pdCompletionUnit U₀ p d₀).comp
          (deltaPDivisionSourceTensorTorsionEquiv D y hpA hg v hv hy).toRingHom := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  let := pdCompletionCommRing R₀ p (p : R₀)
  let := derivedDeltaDivisionCommRing D (p : A) a₀
  exact (Classical.choose_spec
    (existsUnique_deltaPDivisionSourceTensorCompletionEquiv D y hpA hg v hv hy)).1

/-- 実完備化比較は、通常入力環の標準単位上で具体的な入力同型に一致する。 -/
theorem deltaPDivisionSourceTensorCompletionEquiv_unit :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    letI := pdCompletionCommRing R₀ p (p : R₀)
    letI := derivedDeltaDivisionCommRing D (p : A) a₀
    ∀ r : R₀,
      deltaPDivisionSourceTensorCompletionEquiv D y hpA hg v hv hy
        (pdCompletionUnit R₀ p (p : R₀) r) =
      pdCompletionUnit U₀ p d₀ (deltaPDivisionSourceTensorTorsionEquiv D y hpA hg v hv hy r) := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  let := pdCompletionCommRing R₀ p (p : R₀)
  let := derivedDeltaDivisionCommRing D (p : A) a₀
  intro r
  exact RingHom.congr_fun (deltaPDivisionSourceTensorCompletionEquiv_comp_unit D y hpA hg v hv hy) r

/-- 実完備化比較は、元のAから既存候補への標準射を保つ。 -/
theorem deltaPDivisionSourceTensorCompletionEquiv_comp_base :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    letI := pdCompletionCommRing R₀ p (p : R₀)
    letI := derivedDeltaDivisionCommRing D (p : A) a₀
    (deltaPDivisionSourceTensorCompletionEquiv D y hpA hg v hv hy).toRingHom.comp
      ((pdCompletionUnit R₀ p (p : R₀)).comp Algebra.TensorProduct.includeLeftRingHom) =
        derivedDeltaDivisionMap D (p : A) a₀ := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  let := pdCompletionCommRing R₀ p (p : R₀)
  let := derivedDeltaDivisionCommRing D (p : A) a₀
  rw [← RingHom.comp_assoc, deltaPDivisionSourceTensorCompletionEquiv_comp_unit,
    RingHom.comp_assoc, deltaPDivisionSourceTensorTorsionEquiv_comp_base]
  rfl

/-- 逆比較も、旧ねじれ商の実標準単位を実通常テンソル完備化の標準単位へ戻す。 -/
theorem deltaPDivisionSourceTensorCompletionEquiv_symm_unit (r : U₀) :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    letI := pdCompletionCommRing R₀ p (p : R₀)
    letI := derivedDeltaDivisionCommRing D (p : A) a₀
    (deltaPDivisionSourceTensorCompletionEquiv D y hpA hg v hv hy).symm
      (pdCompletionUnit U₀ p d₀ r) =
        pdCompletionUnit R₀ p (p : R₀)
          ((deltaPDivisionSourceTensorTorsionEquiv D y hpA hg v hv hy).symm r) := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  let : Module P₀ P₀ := Algebra.toModule
  let := pdCompletionCommRing R₀ p (p : R₀)
  let := derivedDeltaDivisionCommRing D (p : A) a₀
  apply (deltaPDivisionSourceTensorCompletionEquiv D y hpA hg v hv hy).injective
  rw [RingEquiv.apply_symm_apply, deltaPDivisionSourceTensorCompletionEquiv_unit,
    RingEquiv.apply_symm_apply]

end SerrePositivity.BhattScholze
