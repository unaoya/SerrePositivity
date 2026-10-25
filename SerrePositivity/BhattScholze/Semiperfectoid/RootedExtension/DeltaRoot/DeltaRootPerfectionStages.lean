module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.DeltaRoot.DeltaRootFamilyRawCompletelyFlat
public import SerrePositivity.BhattScholze.Delta.Perfect.DeltaPerfection

/-! # 実raw根族のFrobenius完全化における正確な係数作用 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (b : σ → A)
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) b
local notation "B" => DeltaAdjoinDivision E (p : P)
  (fun s ↦ DeltaStructure.frobeniusLift E (r s))
local notation "F" => deltaAdjoinDivisionStructure E (p : P)
  (fun s ↦ DeltaStructure.frobeniusLift E (r s))
local notation "j" => deltaRootRawCoefficientMap D b
local notation "C" => DeltaPerfection F

/-- n段の係数作用を区別する、既存raw包の標準ULift。 -/
def DeltaRootPerfectionStage (_n : ℕ) := ULift.{0} B

instance deltaRootPerfectionStageCommRing (n : ℕ) :
    CommRing (DeltaRootPerfectionStage D b n) := by
  unfold DeltaRootPerfectionStage
  infer_instance

/-- n段の係数射は実raw Frobeniusのn反復を通る。 -/
def deltaRootPerfectionStageCoefficientMap (n : ℕ) :
    A →+* DeltaRootPerfectionStage D b n :=
  (ULift.ringEquiv.symm.toRingHom).comp (((DeltaStructure.frobeniusLift F) ^ n).comp j)

/-- 段係数射の値は、元のA上のFrobenius反復を実raw係数射で送ったもの。 -/
theorem deltaRootPerfectionStageCoefficientMap_apply (n : ℕ) (a : A) :
    (deltaRootPerfectionStageCoefficientMap D b n a).down =
      j ((DeltaStructure.frobeniusLift D : A → A)^[n] a) := by
  have hj : DeltaStructure.IsDeltaHom D F j :=
    (deltaAdjoinDivisionMap_isDeltaHom E (p : P)
      (fun s ↦ DeltaStructure.frobeniusLift E (r s))).comp
        (polynomialRankOneDeltaStructure_C_isDeltaHom σ D)
  change (DeltaStructure.frobeniusLift F : B → B)^[n] (j a) = _
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      hj.map_frobeniusLift]

/-- n段の正確な係数作用。 -/
abbrev deltaRootPerfectionStageAlgebra (n : ℕ) : Algebra A (DeltaRootPerfectionStage D b n) :=
  (deltaRootPerfectionStageCoefficientMap D b n).toAlgebra

/-- 余極限の係数射は、元のraw係数射と第0段標準射の合成。 -/
def deltaRootPerfectionCoefficientMap : A →+* C := (deltaPerfectionOf F 0).comp j

/-- 既存δ完全化に与える実係数作用。 -/
abbrev deltaRootPerfectionAlgebra : Algebra A C :=
  (deltaRootPerfectionCoefficientMap D b).toAlgebra

attribute [local instance] deltaRootPerfectionStageAlgebra deltaRootPerfectionAlgebra

/-- 第n段から既存の実δ完全化への標準環射。 -/
def deltaRootPerfectionStageMap (n : ℕ) : DeltaRootPerfectionStage D b n →+* C :=
  (deltaPerfectionOf F n).comp ULift.ringEquiv.toRingHom

/-- 全段の実係数射は余極限内で元の係数射と一致する。 -/
theorem deltaRootPerfectionStageMap_comp_coefficient (n : ℕ) :
    (deltaRootPerfectionStageMap D b n).comp (deltaRootPerfectionStageCoefficientMap D b n) =
      deltaRootPerfectionCoefficientMap D b := by
  ext a
  change deltaPerfectionOf F n ((DeltaStructure.frobeniusLift F : B → B)^[n] (j a)) =
    deltaPerfectionOf F 0 (j a)
  simpa only [Nat.sub_zero] using deltaPerfectionOf_iterate F (Nat.zero_le n) (j a)

/-- 実標準段射を、正確な係数作用についてのA代数射として公開する。 -/
def deltaRootPerfectionStageAlgHom (n : ℕ) : DeltaRootPerfectionStage D b n →ₐ[A] C :=
  { deltaRootPerfectionStageMap D b n with
    commutes' := fun a => RingHom.congr_fun (deltaRootPerfectionStageMap_comp_coefficient D b n) a }

/-- 隣接する実Frobenius遷移は、段ごとの係数作用についてA代数射。 -/
def deltaRootPerfectionStageTransition (n : ℕ) :
    DeltaRootPerfectionStage D b n →ₐ[A] DeltaRootPerfectionStage D b (n + 1) :=
  { (ULift.ringEquiv.symm.toRingHom).comp
      ((DeltaStructure.frobeniusLift F).comp ULift.ringEquiv.toRingHom) with
    commutes' := by
      intro a
      change ULift.up (DeltaStructure.frobeniusLift F
        ((DeltaStructure.frobeniusLift F : B → B)^[n] (j a))) =
          ULift.up ((DeltaStructure.frobeniusLift F : B → B)^[n+1] (j a))
      rw [Function.iterate_succ_apply'] }

/-- 第n段と第n+1段から実完全化への標準射は遷移と可換。 -/
theorem deltaRootPerfectionStageAlgHom_transition (n : ℕ) :
    (deltaRootPerfectionStageAlgHom D b (n + 1)).comp
        (deltaRootPerfectionStageTransition D b n) = deltaRootPerfectionStageAlgHom D b n := by
  ext x
  change deltaPerfectionOf F (n + 1) (DeltaStructure.frobeniusLift F x.down) =
    deltaPerfectionOf F n x.down
  exact deltaPerfectionOf_succ_frobenius F n x.down

end SerrePositivity.BhattScholze
