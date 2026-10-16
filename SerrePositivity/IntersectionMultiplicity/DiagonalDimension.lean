module

public import SerrePositivity.IntersectionMultiplicity.DiagonalTor
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.GoingDown

/-! # 対角線の商の次元

## 概要

`R = k[[X]]`、`S = R[[Y]]`、イデアル `P, Q ⊆ R` について `T = S / (PS + Q^{i₂} S)` とする。

\[
\dim T = \dim R/Q + \dim R/P.
\]

## 方針

`E = R/Q → T`（`i₂` から誘導）は平坦：`T ≅ E ⊗_R (S/PS)` で、`S/PS` は `i₂` を通して `R` 上平坦
（`flat_coeffQuot`）。平坦なら going-down が成り立ち、Mathlib の高さの公式
（`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`）から
`ht m_T = ht m_E + ht(m_T / m_E T)`。閉ファイバー `T / m_E T` は定数項を取る写像で `R/P` と同型。

## 使われ方

解説の付録 A（「引用している結果」の対角線論法の段落）の工程（次元公式 $\dim T=\dim D+\dim E$）。
`dim R/P + dim R/Q = d` のとき `dim T = d` となり、`δ` が `T` のパラメータ系になる。
-/

@[expose] public noncomputable section

universe u

open IsLocalRing MvPowerSeries TensorProduct

namespace SerrePositivity.DiagonalRing

variable (k : Type u) [Field k] (d : ℕ)

local notation "𝓡" => MvPowerSeries (Fin d) k

variable (P Q : Ideal (MvPowerSeries (Fin d) k))

theorem varIdeal_le : varIdeal k d Q ≤ coeffIdeal k d P ⊔ varIdeal k d Q := le_sup_right

/-- `E = R/Q → T`（変数の取り替えから誘導）。 -/
def quotMap : 𝓡 ⧸ Q →+* diagonalQuot k d P Q :=
  Ideal.quotientMap (coeffIdeal k d P ⊔ varIdeal k d Q) (algebraMap 𝓡 (DiagonalRing k d))
    (Ideal.map_le_iff_le_comap.mp (varIdeal_le k d P Q))

@[simp] theorem quotMap_mk (r : 𝓡) :
    quotMap k d P Q (Ideal.Quotient.mk Q r) =
      Ideal.Quotient.mk _ (algebraMap 𝓡 (DiagonalRing k d) r) := rfl

/-- 環としての同型 `R/Q ⊗_R S/PS ≅ T`。 -/
def tensorRingEquiv :
    ((𝓡 ⧸ Q) ⊗[𝓡] coeffQuot k d P) ≃+* diagonalQuot k d P Q := by
  let D' := coeffQuot k d P
  have hJ : Q.map (algebraMap 𝓡 D') =
      (varIdeal k d Q).map (Ideal.Quotient.mk (coeffIdeal k d P)) := by
    simp only [varIdeal, Ideal.map_map]
    rfl
  exact (Algebra.TensorProduct.comm 𝓡 (𝓡 ⧸ Q) D').toRingEquiv.trans
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot D' Q).symm.toRingEquiv.trans
      ((Ideal.quotEquivOfEq hJ).trans (DoubleQuot.quotQuotEquivQuotSup _ _)))

theorem tensorRingEquiv_tmul_one (r : 𝓡) :
    tensorRingEquiv k d P Q (Ideal.Quotient.mk Q r ⊗ₜ 1) = quotMap k d P Q (Ideal.Quotient.mk Q r) := by
  have h1 : (1 : coeffQuot k d P) ⊗ₜ[𝓡] (Ideal.Quotient.mk Q r) =
      (algebraMap 𝓡 (coeffQuot k d P) r) ⊗ₜ[𝓡] (1 : 𝓡 ⧸ Q) := by
    have : Ideal.Quotient.mk Q r = r • (1 : 𝓡 ⧸ Q) := by
      rw [← Algebra.algebraMap_eq_smul_one]
      rfl
    rw [this, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.algebraMap_eq_smul_one]
  simp only [tensorRingEquiv, RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv, Algebra.TensorProduct.comm_tmul, quotMap_mk]
  rw [h1]
  have h2 : (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (coeffQuot k d P) Q).symm
      ((algebraMap 𝓡 (coeffQuot k d P)) r ⊗ₜ[𝓡] 1) =
        Ideal.Quotient.mk _ (algebraMap 𝓡 (coeffQuot k d P) r) := by
    rw [AlgEquiv.symm_apply_eq, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
  rw [h2, Ideal.quotEquivOfEq_mk]
  exact DoubleQuot.quotQuotEquivQuotSup_quotQuotMk _ _ _

/-- `E = R/Q → T` は平坦。`T ≅ E ⊗_R S/PS` で、`S/PS` は `R` 上平坦。 -/
theorem flat_quotMap : (quotMap k d P Q).Flat := by
  let : Algebra (𝓡 ⧸ Q) (diagonalQuot k d P Q) := (quotMap k d P Q).toAlgebra
  have : Module.Flat 𝓡 (coeffQuot k d P) := flat_coeffQuot k d P
  let e : ((𝓡 ⧸ Q) ⊗[𝓡] coeffQuot k d P) ≃ₗ[𝓡 ⧸ Q] diagonalQuot k d P Q :=
    { toFun := tensorRingEquiv k d P Q
      invFun := (tensorRingEquiv k d P Q).symm
      left_inv := (tensorRingEquiv k d P Q).left_inv
      right_inv := (tensorRingEquiv k d P Q).right_inv
      map_add' := map_add _
      map_smul' := fun c x ↦ by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
        change tensorRingEquiv k d P Q (Ideal.Quotient.mk Q r • x) =
          quotMap k d P Q (Ideal.Quotient.mk Q r) * tensorRingEquiv k d P Q x
        induction x with
        | tmul a b =>
          have : Ideal.Quotient.mk Q r • (a ⊗ₜ[𝓡] b) =
              (Ideal.Quotient.mk Q r ⊗ₜ[𝓡] (1 : coeffQuot k d P)) * (a ⊗ₜ b) := by
            rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.smul_tmul',
              smul_eq_mul]
          rw [this, map_mul, tensorRingEquiv_tmul_one]
        | add y z hy hz => rw [smul_add, map_add, map_add, hy, hz, mul_add] }
  exact Module.Flat.of_linearEquiv e.symm

/-- 体係数の冪級数環の極大イデアルの元は定数項が零。 -/
theorem constantCoeff_eq_zero_of_mem {r : 𝓡} (hr : r ∈ maximalIdeal 𝓡) :
    MvPowerSeries.constantCoeff r = 0 := by
  by_contra h
  exact (mem_maximalIdeal r).mp hr (MvPowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr h))

theorem coeffIdeal_sup_varIdeal_ne_top (hP : P ≠ ⊤) (hQ : Q ≠ ⊤) :
    coeffIdeal k d P ⊔ varIdeal k d Q ≠ ⊤ := by
  apply ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top
  refine sup_le ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    exact const_mem_maximalIdeal k d (le_maximalIdeal hP ha)
  · exact (Ideal.map_mono (le_maximalIdeal hQ)).trans (map_maximalIdeal_le _)

/-- 定数項 `S → R`。 -/
def constCoeff : DiagonalRing k d →+* 𝓡 :=
  (MvPowerSeries.constantCoeff (σ := Fin d) (R := 𝓡)).comp (toPS k d).toRingHom

/-- 定数項を取る写像 `T → R/P`。 -/
def fibreMap (hQ : Q ≠ ⊤) : diagonalQuot k d P Q →+* 𝓡 ⧸ P :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk P).comp (constCoeff k d)) (by
      intro f hf
      have hle : coeffIdeal k d P ⊔ varIdeal k d Q ≤
          RingHom.ker ((Ideal.Quotient.mk P).comp (constCoeff k d)) := by
        refine sup_le ?_ ?_
        · rw [Ideal.map_le_iff_le_comap]
          intro p hp
          simp only [Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply]
          change Ideal.Quotient.mk P (MvPowerSeries.constantCoeff (MvPowerSeries.C p)) = 0
          rw [MvPowerSeries.constantCoeff_C, Ideal.Quotient.eq_zero_iff_mem]
          exact hp
        · rw [Ideal.map_le_iff_le_comap]
          intro q hq
          simp only [Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply]
          change Ideal.Quotient.mk P (MvPowerSeries.constantCoeff
            (MvPowerSeries.map (MvPowerSeries.C (σ := Fin d) (R := k)) q)) = 0
          rw [MvPowerSeries.constantCoeff_map,
            constantCoeff_eq_zero_of_mem k d (le_maximalIdeal hQ hq), map_zero, map_zero]
      exact hle hf)

theorem fibreMap_mk (hQ : Q ≠ ⊤) (f : DiagonalRing k d) :
    fibreMap k d P Q hQ (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk P (MvPowerSeries.constantCoeff (toPS k d f)) := rfl

theorem fibreMap_surjective (hQ : Q ≠ ⊤) : Function.Surjective (fibreMap k d P Q hQ) := by
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨Ideal.Quotient.mk _ (const k d a), ?_⟩
  rw [fibreMap_mk]
  change Ideal.Quotient.mk P (MvPowerSeries.constantCoeff (MvPowerSeries.C a)) = _
  rw [MvPowerSeries.constantCoeff_C]

section dimension

variable (hP : P ≠ ⊤) (hQ : Q ≠ ⊤)

/-- `T` は局所環。 -/
abbrev localDiagonalQuot : IsLocalRing (diagonalQuot k d P Q) :=
  have : Nontrivial (diagonalQuot k d P Q) :=
    Ideal.Quotient.nontrivial_iff.mpr (coeffIdeal_sup_varIdeal_ne_top k d P Q hP hQ)
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- `E = R/Q` は局所環。 -/
abbrev localQuot : IsLocalRing (𝓡 ⧸ Q) :=
  have : Nontrivial (𝓡 ⧸ Q) := Ideal.Quotient.nontrivial_iff.mpr hQ
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

include hP hQ in
/-- `E → T` は局所準同型。 -/
theorem isLocalHom_quotMap :
    letI := localDiagonalQuot k d P Q hP hQ
    letI := localQuot k d Q hQ
    IsLocalHom (quotMap k d P Q) := by
  let := localDiagonalQuot k d P Q hP hQ
  let := localQuot k d Q hQ
  constructor
  intro a ha
  by_contra hna
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hr : r ∈ maximalIdeal 𝓡 := by
    have : Ideal.Quotient.mk Q r ∈ maximalIdeal (𝓡 ⧸ Q) := (mem_maximalIdeal _).mpr hna
    have hloc : IsLocalHom (Ideal.Quotient.mk Q) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    rw [← maximalIdeal_comap (Ideal.Quotient.mk Q)]
    exact this
  have hS : algebraMap 𝓡 (DiagonalRing k d) r ∈ maximalIdeal (DiagonalRing k d) :=
    map_maximalIdeal_le (algebraMap 𝓡 (DiagonalRing k d)) (Ideal.mem_map_of_mem _ hr)
  have hloc : IsLocalHom (Ideal.Quotient.mk (coeffIdeal k d P ⊔ varIdeal k d Q)) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hT : quotMap k d P Q (Ideal.Quotient.mk Q r) ∈ maximalIdeal (diagonalQuot k d P Q) :=
    map_maximalIdeal_le (Ideal.Quotient.mk _) (Ideal.mem_map_of_mem _ hS)
  exact (mem_maximalIdeal _).mp hT ha

/-- 閉ファイバー：`ker(T → R/P) = m_E T`。 -/
theorem ker_fibreMap :
    letI := localQuot k d Q hQ
    RingHom.ker (fibreMap k d P Q hQ) = (maximalIdeal (𝓡 ⧸ Q)).map (quotMap k d P Q) := by
  let := localQuot k d Q hQ
  have hmE : ∀ r ∈ maximalIdeal 𝓡,
      quotMap k d P Q (Ideal.Quotient.mk Q r) ∈ (maximalIdeal (𝓡 ⧸ Q)).map (quotMap k d P Q) := by
    intro r hr
    apply Ideal.mem_map_of_mem
    have hloc : IsLocalHom (Ideal.Quotient.mk Q) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    exact map_maximalIdeal_le (Ideal.Quotient.mk Q) (Ideal.mem_map_of_mem _ hr)
  apply le_antisymm
  · intro t ht
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective t
    have hcc : constCoeff k d f ∈ P := by
      rw [RingHom.mem_ker, fibreMap_mk, Ideal.Quotient.eq_zero_iff_mem] at ht
      exact ht
    -- `f = (f − C(f₀)) + C(f₀)`、前者は変数のイデアル、後者は `PS`
    have h1 : f - const k d (constCoeff k d f) ∈ Ideal.span (Set.range (var k d)) := by
      have := powerSeries_ker_constantCoeff (Fin d) 𝓡
      have hm : toPS k d (f - const k d (constCoeff k d f)) ∈
          RingHom.ker (MvPowerSeries.constantCoeff (σ := Fin d) (R := 𝓡)) := by
        rw [RingHom.mem_ker]
        change MvPowerSeries.constantCoeff (toPS k d f - MvPowerSeries.C (constCoeff k d f)) = 0
        rw [map_sub, MvPowerSeries.constantCoeff_C]
        change constCoeff k d f - constCoeff k d f = 0
        exact sub_self _
      rw [this] at hm
      exact hm
    have h2 : Ideal.Quotient.mk (coeffIdeal k d P ⊔ varIdeal k d Q) (const k d (constCoeff k d f)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hcc))
    have hspan : (Ideal.span (Set.range (var k d))).map
        (Ideal.Quotient.mk (coeffIdeal k d P ⊔ varIdeal k d Q)) ≤
          (maximalIdeal (𝓡 ⧸ Q)).map (quotMap k d P Q) := by
      rw [Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      have := hmE (MvPowerSeries.X i) (X_mem_maximalIdeal k d i)
      rwa [quotMap_mk, algebraMap_X] at this
    have : f = (f - const k d (constCoeff k d f)) + const k d (constCoeff k d f) := by ring
    rw [this, map_add, h2, add_zero]
    exact hspan (Ideal.mem_map_of_mem _ h1)
  · rw [Ideal.map_le_iff_le_comap]
    intro e he
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective e
    have hr : r ∈ maximalIdeal 𝓡 := by
      have hloc : IsLocalHom (Ideal.Quotient.mk Q) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      rw [← maximalIdeal_comap (Ideal.Quotient.mk Q)]
      exact he
    rw [Ideal.mem_comap, RingHom.mem_ker, quotMap_mk, fibreMap_mk]
    change Ideal.Quotient.mk P (MvPowerSeries.constantCoeff
      (MvPowerSeries.map (MvPowerSeries.C (σ := Fin d) (R := k)) r)) = 0
    rw [MvPowerSeries.constantCoeff_map, constantCoeff_eq_zero_of_mem k d hr, map_zero, map_zero]

include hP hQ in
/-- **対角線の商の次元**：`dim T = dim R/Q + dim R/P`。平坦な `E = R/Q → T` の高さの公式と、
閉ファイバー `T/m_E T ≅ R/P` による。 -/
theorem ringKrullDim_diagonalQuot :
    ringKrullDim (diagonalQuot k d P Q) = ringKrullDim (𝓡 ⧸ Q) + ringKrullDim (𝓡 ⧸ P) := by
  let := localDiagonalQuot k d P Q hP hQ
  let := localQuot k d Q hQ
  let : Algebra (𝓡 ⧸ Q) (diagonalQuot k d P Q) := (quotMap k d P Q).toAlgebra
  have : Module.Flat (𝓡 ⧸ Q) (diagonalQuot k d P Q) := flat_quotMap k d P Q
  have hloc := isLocalHom_quotMap k d P Q hP hQ
  have : (maximalIdeal (diagonalQuot k d P Q)).LiesOver (maximalIdeal (𝓡 ⧸ Q)) :=
    ⟨(maximalIdeal_comap (quotMap k d P Q)).symm⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal (𝓡 ⧸ Q))
    (maximalIdeal (diagonalQuot k d P Q))
  -- 閉ファイバー
  set I := (maximalIdeal (𝓡 ⧸ Q)).map (algebraMap (𝓡 ⧸ Q) (diagonalQuot k d P Q))
  have hI : I = RingHom.ker (fibreMap k d P Q hQ) := (ker_fibreMap k d P Q hQ).symm
  let eF : (diagonalQuot k d P Q ⧸ I) ≃+* 𝓡 ⧸ P :=
    (Ideal.quotEquivOfEq hI).trans
      (RingHom.quotientKerEquivOfSurjective (fibreMap_surjective k d P Q hQ))
  have : Nontrivial (diagonalQuot k d P Q ⧸ I) := by
    have hP' : Nontrivial (𝓡 ⧸ P) := Ideal.Quotient.nontrivial_iff.mpr hP
    exact eF.toEquiv.nontrivial
  let : IsLocalRing (diagonalQuot k d P Q ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hF : (maximalIdeal (diagonalQuot k d P Q)).map (Ideal.Quotient.mk I) =
      maximalIdeal (diagonalQuot k d P Q ⧸ I) :=
    map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  rw [hF] at h
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h,
    ← RingEquiv.ringKrullDim eF, ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  push_cast
  rfl

end dimension

end SerrePositivity.DiagonalRing
