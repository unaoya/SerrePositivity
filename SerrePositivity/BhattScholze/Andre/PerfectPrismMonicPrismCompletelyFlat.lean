module

public import SerrePositivity.BhattScholze.Andre.PerfectPrismMonicPDPerfectionInputs
public import SerrePositivity.BhattScholze.Andre.MonicPrismaticCandidateComparison
public import SerrePositivity.CommutativeAlgebra.CompletelyFlatEquiv

/-!
# André E1・E2：有限モニック族の既存 prism 候補の完全忠実平坦性

## 概要

完全 prism 上の有限正次数モニック族の既存多項式 prism 候補は、標準係数射に関して
元の (p,d) 上完全忠実平坦。BS Rem 7.15（著者版 p.62）の具体的候補への平坦性。

## 方針

PD 先行 δ 完全化で得た平坦性を、元の係数射を保つ具体的環・加群同型で既存候補へ移す。
原典の Prop 7.11 を使う証明とは異なる経路の計算。

## 規約

標準係数射の toAlgebra を明示する。perfectoid 商上の p 完全忠実平坦性は別工程。

## 使われ方

既存の根方程式と整 perfectoid 性を持つ商候補へ p 完全忠実平坦性を移す。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (f : σ → Polynomial A)
variable (hf : ∀ t, (f t).Monic) (hdeg : ∀ t, 0 < (f t).natDegree)
variable {m : ℕ} (eσ : Fin m ≃ σ)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => (fun t : σ => monicRelation (f t) t)
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "F" => deltaAdjoinDivisionStructure E (MvPolynomial.C d) r
local notation "c" => algebraMap A Raw
local notation "z" => c d
local notation "G" => deltaPDCompletionStructure F z
local notation "v" => pdCompletionUnit Raw p z
local notation "j" => RingHom.comp v c
local notation "C" => DeltaPerfection G
local notation "κ" => deltaAlgebraPerfectionCoefficient G j
local notation "t" => RingHom.comp (pdCompletionUnit C p (κ d)) κ
local notation "T" => DivisionPrismCarrier E (MvPolynomial.C d) r
local notation "φ" => polynomialPrismCoefficientMap D d f
local notation "I" => Ideal.span {(p : A), d}
include hP hf hdeg eσ

/-- 概要：有限正次数モニック族の既存多項式 prism 候補は、標準係数射の作用で完全忠実平坦。
方針：PD 先行完全化の平坦性を係数射を保つ加群同型で移し、toAlgebra の作用と照合する。
規約：元の (p,d) と同じ係数射を使う。有限全列挙以外の補助仮定を残さない。
使われ方：BS Rem 7.15（著者版 p.62）の最終 perfectoid 商の平坦性への入力。 -/
theorem perfectPrismMonicPrism_isCompletelyFaithfullyFlat :
    letI := polynomialPrismCommRing D d f
    letI := (φ).toAlgebra
    IsCompletelyFaithfullyFlat I T := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing C p (κ d)
  let := polynomialPrismCommRing D d f
  have hM : IsCompletelyFaithfullyFlat I (ModuleCat.carrier (baseChangeScalarModule φ)) :=
    isCompletelyFaithfullyFlat_of_linearEquiv I
      (monicPrismaticPDPerfectionCandidateModuleIso D d f).toLinearEquiv
      (perfectPrismMonicPDPerfection_isCompletelyFaithfullyFlat P hP f hf hdeg eσ)
  let := (φ).toAlgebra
  let e : baseChangeScalarModule φ ≃ₗ[A] T :=
    { toFun := fun y => y
      invFun := fun y => y
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a y
        rw [RingHom.id_apply, ModuleCat.restrictScalars.smul_def] }
  exact isCompletelyFaithfullyFlat_of_linearEquiv I e hM

end SerrePositivity.BhattScholze.Andre
