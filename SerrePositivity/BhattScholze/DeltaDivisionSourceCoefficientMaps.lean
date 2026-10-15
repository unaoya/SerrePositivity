module

public import SerrePositivity.BhattScholze.DeltaDivisionSourceCoefficientReduction

/-! # 自由δ射の係数商への標準降下

任意の係数イデアルを扱い、商のδ構造は要求しない。
自由δ射の商への降下と標準自己射を区別する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (I : Ideal A)
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "J₀" => I.map (MvPolynomial.C : A →+* P₀)
local notation "Q₀" => P₀ ⧸ J₀
local notation "β₀" => deltaDivisionSourceEval D a
local notation "α₀" => deltaDivisionSourceMap (σ := σ) D d

/-- 実評価βの係数商への標準降下。 -/
def deltaDivisionSourceCoefficientEvalMap : Q₀ →+* A ⧸ I :=
  Ideal.quotientMap I β₀ (Ideal.map_le_iff_le_comap.mp
    (le_of_eq (deltaDivisionSourceEvaluation_coefficientIdeal_map D a I)))

/-- 実自由δ射αの係数商への標準降下。 -/
def deltaDivisionSourceCoefficientTargetMap : Q₀ →+* Q₀ :=
  Ideal.quotientMap J₀ α₀ (Ideal.map_le_iff_le_comap.mp
    (le_of_eq (deltaDivisionSourceTarget_coefficientIdeal_map (σ := σ) D d I)))

/-- 係数包含の商への標準降下。 -/
def deltaDivisionSourceCoefficientBaseMap : A ⧸ I →+* Q₀ :=
  Ideal.quotientMap J₀ (MvPolynomial.C : A →+* P₀)
    (Ideal.map_le_iff_le_comap.mp le_rfl)

/-- βの降下は、標準商代表元の実評価で与えられる。 -/
theorem deltaDivisionSourceCoefficientEvalMap_mk (r : P₀) :
    deltaDivisionSourceCoefficientEvalMap D a I (Ideal.Quotient.mk J₀ r) =
      Ideal.Quotient.mk I (β₀ r) :=
  Ideal.quotientMap_mk

/-- αの降下は、標準商代表元の実自由δ像で与えられる。 -/
theorem deltaDivisionSourceCoefficientTargetMap_mk (r : P₀) :
    deltaDivisionSourceCoefficientTargetMap (σ := σ) D d I (Ideal.Quotient.mk J₀ r) =
      Ideal.Quotient.mk J₀ (α₀ r) :=
  Ideal.quotientMap_mk

/-- 係数包含の降下は、係数の標準商像を保つ。 -/
theorem deltaDivisionSourceCoefficientBaseMap_mk (r : A) :
    deltaDivisionSourceCoefficientBaseMap (σ := σ) I (Ideal.Quotient.mk I r) =
      Ideal.Quotient.mk J₀ (MvPolynomial.C r) :=
  Ideal.quotientMap_mk

/-- βの標準降下の商射との可換図式。 -/
theorem deltaDivisionSourceCoefficientEvalMap_comp_quotient :
    (deltaDivisionSourceCoefficientEvalMap D a I).comp (Ideal.Quotient.mk J₀) =
      (Ideal.Quotient.mk I).comp β₀ := by
  apply RingHom.ext
  intro r
  exact deltaDivisionSourceCoefficientEvalMap_mk D a I r

/-- αの標準降下の商射との可換図式。 -/
theorem deltaDivisionSourceCoefficientTargetMap_comp_quotient :
    (deltaDivisionSourceCoefficientTargetMap (σ := σ) D d I).comp (Ideal.Quotient.mk J₀) =
      (Ideal.Quotient.mk J₀).comp α₀ := by
  apply RingHom.ext
  intro r
  exact deltaDivisionSourceCoefficientTargetMap_mk D d I r

/-- 商への降下後も、実評価は係数包含の左逆。 -/
theorem deltaDivisionSourceCoefficientEvalMap_comp_base :
    (deltaDivisionSourceCoefficientEvalMap D a I).comp
      (deltaDivisionSourceCoefficientBaseMap (σ := σ) I) = RingHom.id (A ⧸ I) := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro r
  change deltaDivisionSourceCoefficientEvalMap D a I
    (deltaDivisionSourceCoefficientBaseMap (σ := σ) I (Ideal.Quotient.mk I r)) = _
  rw [deltaDivisionSourceCoefficientBaseMap_mk, deltaDivisionSourceCoefficientEvalMap_mk,
    deltaDivisionSourceEval_C]
  rfl

/-- 商へ降下した自由δ射は係数包含を固定する。自己射と同一視はしない。 -/
theorem deltaDivisionSourceCoefficientTargetMap_comp_base :
    (deltaDivisionSourceCoefficientTargetMap (σ := σ) D d I).comp
      (deltaDivisionSourceCoefficientBaseMap (σ := σ) I) =
        deltaDivisionSourceCoefficientBaseMap (σ := σ) I := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro r
  change deltaDivisionSourceCoefficientTargetMap D d I
    (deltaDivisionSourceCoefficientBaseMap (σ := σ) I (Ideal.Quotient.mk I r)) = _
  rw [deltaDivisionSourceCoefficientBaseMap_mk, deltaDivisionSourceCoefficientTargetMap_mk,
    deltaDivisionSourceMap_C]
  rfl

end SerrePositivity.BhattScholze
