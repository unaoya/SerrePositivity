module

public import SerrePositivity.BhattScholze.Prismatic.Envelopes.VariableEnvelopeBaseChange
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.CompletedFreeDeltaScale
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeConstruction
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeConstruction
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeMaps
import all SerrePositivity.BhattScholze.Prismatic.Envelopes.VariableEnvelope

/-!
# affine 包の座標を保つ完備底変換

## 概要
prism の射による affine 包の完備底変換を、各頂点の座標を保って同定する。

## 方針
K4 の自由 δ 環の底変換を使い、生成元の単元倍を差の分母座標の逆単元倍で補正する。

## 規約
余単体次数と変数の数を固定する。両側の濃度上限は独立に選べる。

## 使われ方
BS 著者版 Proposition 3.13 (2) と Theorem 6.4 の有限 affine 枠。
-/

public noncomputable section

attribute [local instance] Classical.propDecidable

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false

variable {p : ℕ} [Fact p.Prime] {A A' : Type u} [CommRing A] [CommRing A']
variable (P : OrientedPrism p A) (P' : OrientedPrism p A') (f : OrientedPrism.Hom P P')
variable (r n : ℕ)

local notation "S" => AffineIndex r n
local notation "Src" => completedFreeDelta P S
local notation "Tgt" => completedFreeDelta P' S
local notation "b" => completedFreeDeltaBase P S
local notation "b'" => completedFreeDeltaBase P' S
local notation "X" => completedFreeDeltaVariable P S
local notation "X'" => completedFreeDeltaVariable P' S

private theorem envelope_vertex (j : Fin r) (i : Fin (n + 1)) :
    affineEnvelopeUnit P r n (affineVariable P r n j i) =
      if i = 0 then X ⟨(j,0)⟩ else b P.generator * X ⟨(j,i)⟩ + X ⟨(j,0)⟩ := by
  change variableEnvelopeSubstitution P S (differenceCoordinates r n)
    (affineShift P r n 1 (X ⟨(j,i)⟩)) = _
  have hsub (s : S) : variableEnvelopeSubstitution P S (differenceCoordinates r n) (X s) =
      if s.down.2 ≠ 0 then b P.generator * X s else X s := by
    by_cases hs : s.down.2 ≠ 0 <;>
      simpa [scaleCoordinate, differenceCoordinates, hs] using
        (variableEnvelopeSubstitution_spec P S (differenceCoordinates r n)).2.2 s
  rw [(affineShift_spec P r n 1).2.2]
  by_cases hi : i = 0 <;> simp [shiftValue, hi, hsub]

private theorem free_affine_baseChange :
    letI := f.toRingHom.toAlgebra
    letI := (b).toAlgebra
    let D := prismCompletedTensorDelta P' P.deltaStructure
      (completedFreeDeltaStructure P S) f.map_delta (completedFreeDeltaBase_isDeltaHom P S)
    ∃ e : PrismCompletedTensor (A := A) (C := Src) P' ≃+* Tgt,
      D.IsDeltaHom (completedFreeDeltaStructure P' S) e.toRingHom ∧
      e.toRingHom.comp (prismCompletedTensorLeft P') = b' ∧
      ∀ j i, e (prismCompletedTensorRight P'
        (affineEnvelopeUnit P r n (affineVariable P r n j i))) =
          affineEnvelopeUnit P' r n (affineVariable P' r n j i) := by
  let := f.toRingHom.toAlgebra
  let := (b).toAlgebra
  obtain ⟨u, hu⟩ := f.map_generator_unit_mul
  obtain ⟨e₀, hδ, hb, hx⟩ := exists_completedFreeDelta_baseChange_equiv P P' f S
  obtain ⟨σ, hσδ, hσb, hσx⟩ := exists_completedFreeDeltaScaleEquiv
    P' S (differenceCoordinates r n) u⁻¹
  let e := e₀.trans σ
  have hleft : e.toRingHom.comp (prismCompletedTensorLeft P') = b' := by
    change σ.toRingHom.comp (e₀.toRingHom.comp (prismCompletedTensorLeft P')) = b'
    rw [hb, hσb]
  have hbase (a : A) : e (prismCompletedTensorRight P' (b a)) = b' (f.toRingHom a) := by
    have h := RingHom.congr_fun (prismCompletedTensor_square (A := A) (C := Src) P') a
    change prismCompletedTensorLeft P' (f.toRingHom a) =
      prismCompletedTensorRight P' (b a) at h
    rw [← h]
    exact RingHom.congr_fun hleft _
  have hvar (s : S) : e (prismCompletedTensorRight P' (X s)) =
      if s.down.2 ≠ 0 then b' (↑u⁻¹) * X' s else X' s := by
    change σ (e₀ (prismCompletedTensorRight P' (X s))) = _
    rw [hx]
    by_cases hs : s.down.2 ≠ 0 <;> simpa [differenceCoordinates, hs] using hσx s
  refine ⟨e, hσδ.comp hδ, hleft, ?_⟩
  intro j i
  rw [envelope_vertex, envelope_vertex]
  by_cases hi : i = 0
  · subst i
    simpa using hvar ⟨(j,0)⟩
  · have hu' : b' (f.toRingHom P.generator) * b' (↑u⁻¹) = b' P'.generator := by
      rw [← map_mul, hu, mul_assoc, Units.mul_inv, mul_one]
    simp only [map_add, map_mul, hbase, hvar,
      hi, not_false_eq_true, ite_true, ne_eq, not_true_eq_false, ite_false,
      ← mul_assoc, hu']

variable (hP : IsBoundedPrism P) (hP' : IsBoundedPrism P')
variable (κ κ' : Cardinal.{u})
variable (hκ : cutoff A (prismPolynomialCompletion P (Fin r)) ≤ κ)
variable (hκ' : cutoff A' (prismPolynomialCompletion P' (Fin r)) ≤ κ')

local notation "U" => affineEnvelopeTerm P hP r n κ hκ
local notation "V" => affineEnvelopeTerm P' hP' r n κ' hκ'

private theorem standard_affine_base : (U).X.toHom.toRingHom = b :=
  affineEnvelopeUnit_base P r n

private theorem standard_affine_base' : (V).X.toHom.toRingHom = b' :=
  affineEnvelopeUnit_base P' r n

private theorem standard_affine_baseChange :
    letI := f.toRingHom.toAlgebra
    letI := (U).X.toHom.toRingHom.toAlgebra
    ∃ e : PrismCompletedTensor (A := A) (C := (U).X.B) P' ≃+* (V).X.B,
      (U).X.Q.deltaStructure.IsDeltaHom (V).X.Q.deltaStructure
        (e.toRingHom.comp (prismCompletedTensorRight P')) ∧
      e.toRingHom.comp (prismCompletedTensorLeft P') = (V).X.toHom.toRingHom ∧
      ∀ j i, e (prismCompletedTensorRight P' ((U).η (affineVariable P r n j i))) =
        (V).η (affineVariable P' r n j i) := by
  rw [standard_affine_base P r n hP κ hκ, standard_affine_base' P' r n hP' κ' hκ']
  let := f.toRingHom.toAlgebra
  let := (b).toAlgebra
  obtain ⟨e, hδ, hl, hx⟩ := free_affine_baseChange P P' f r n
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [affineEnvelopeTerm, affineEnvelopeTermAux] using e
  · simpa only [affineEnvelopeTerm, affineEnvelopeTermAux, completedFreeDeltaPrism,
      OrientedPrism.ofDistinguished, id_eq] using hδ.comp
        (prismCompletedTensorRight_isDeltaHom P' P.deltaStructure
          (completedFreeDeltaStructure P S) f.map_delta (completedFreeDeltaBase_isDeltaHom P S))
  · simpa only [affineEnvelopeTerm, affineEnvelopeTermAux, id_eq] using hl
  · simpa only [affineEnvelopeTerm, affineEnvelopeTermAux, id_eq] using hx

/-- 標準 affine 包の完備底変換は、δ 構造、係数脚と各頂点の座標を保つ。 -/
theorem exists_affineEnvelopeBaseChange_equiv :
    letI := f.toRingHom.toAlgebra
    letI := (U).X.toHom.toRingHom.toAlgebra
    ∃ e : PrismCompletedTensor (A := A) (C := (U).X.B) P' ≃+* (V).X.B,
      (U).X.Q.deltaStructure.IsDeltaHom (V).X.Q.deltaStructure
        (e.toRingHom.comp (prismCompletedTensorRight P')) ∧
      e.toRingHom.comp (prismCompletedTensorLeft P') = (V).X.toHom.toRingHom ∧
      ∀ j i, e (prismCompletedTensorRight P' ((U).η (affineVariable P r n j i))) =
        (V).η (affineVariable P' r n j i) :=
  standard_affine_baseChange P P' f r n hP hP' κ κ' hκ hκ'

end SerrePositivity.BhattScholze.Prismatic
