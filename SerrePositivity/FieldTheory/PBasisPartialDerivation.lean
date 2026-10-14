module

public import SerrePositivity.FieldTheory.PBasisComplement
public import SerrePositivity.FieldTheory.PBasisDifferentials
public import SerrePositivity.FieldTheory.RelativePBasisDifferentials

/-! # p-basis の偏導分と通常微分の基底

各方向の補中間体上の導分を p 乗部分体上へ制限し、微分の独立性を検出する。
添字の有限性は基底の構成に要求しない。
-/

@[expose] public section
namespace SerrePositivity

variable {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
variable {ι : Type*} {b : ι → K}

open Classical in
/-- p-basis の一方向を1、他の方向を0に送る偏導分が存在する。 -/
theorem IsPBasis.exists_partialDerivation (hb : IsPBasis K p b) (i : ι) :
    ∃ δ : Derivation (pPowerSubfield K p) K K,
      ∀ j, δ (b j) = if j = i then 1 else 0 := by
  exact exists_partialDerivation_of_pMonomialBasis hb.basis hb.basis_apply
    (fun j ↦ ⟨⟨b j ^ p, (mem_pPowerSubfield K p _).mpr ⟨b j, rfl⟩⟩, rfl⟩) i

/-- 構成済みの偏導分を選ぶ。 -/
noncomputable def IsPBasis.partialDerivation (hb : IsPBasis K p b) (i : ι) :
    Derivation (pPowerSubfield K p) K K := (hb.exists_partialDerivation i).choose

open Classical in
@[simp] theorem IsPBasis.partialDerivation_apply (hb : IsPBasis K p b) (i j : ι) :
    hb.partialDerivation i (b j) = if j = i then 1 else 0 :=
  (hb.exists_partialDerivation i).choose_spec j

/-- 各偏導分で係数を検出すると、p-basis の通常微分は独立。 -/
theorem IsPBasis.linearIndependent_kaehlerDifferential (hb : IsPBasis K p b) :
    LinearIndependent K (fun i ↦ KaehlerDifferential.D (pPowerSubfield K p) K (b i)) := by
  exact linearIndependent_differential_of_pMonomialBasis hb.basis hb.basis_apply
    (fun j ↦ ⟨⟨b j ^ p, (mem_pPowerSubfield K p _).mpr ⟨b j, rfl⟩⟩, rfl⟩)

/-- 無限添字を許す、p-basis の微分からなる実際の基底。 -/
noncomputable def IsPBasis.kaehlerBasis (hb : IsPBasis K p b) :
    Module.Basis ι K (KaehlerDifferential (pPowerSubfield K p) K) :=
  Module.Basis.mk hb.linearIndependent_kaehlerDifferential (by rw [hb.span_kaehlerDifferential])

@[simp] theorem IsPBasis.kaehlerBasis_apply (hb : IsPBasis K p b) (i : ι) :
    hb.kaehlerBasis i = KaehlerDifferential.D (pPowerSubfield K p) K (b i) :=
  Module.Basis.mk_apply _ _ _

/-- 有限 p-basis の場合の通常微分の次元。 -/
theorem IsPBasis.finrank_kaehlerDifferential [Fintype ι] (hb : IsPBasis K p b) :
    Module.finrank K (KaehlerDifferential (pPowerSubfield K p) K) = Fintype.card ι :=
  Module.finrank_eq_card_basis hb.kaehlerBasis

end SerrePositivity
