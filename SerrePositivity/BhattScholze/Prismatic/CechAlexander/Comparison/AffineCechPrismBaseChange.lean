module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensorRingMaps
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.BaseChange.AffineEnvelopeBaseChangeCoefficients
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeMaps

/-!
# affine Čech–Alexander 模型の prism としての底変換

## 概要
項ごとの完備テンソル積に prism 構造を与え、係数変更を両脚と δ 構造を保つ同型にする。
## 方針
既存の affine 底変換の環同型を使う。両脚から δ 射性を得て、生成元の正則性を同型で検出する。
## 規約
BS 著者版 Remark 4.19・Proposition 3.13 (2)。生成元の厳密な保存は仮定しない。
## 使われ方
底変換の余単体的比較の項ごとの入力。Tot や Δ との同定は含めない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Prismatic
open DerivedCompletion
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {P' : OrientedPrism p B} (f : OrientedPrism.Hom P P')
variable {r n : ℕ} {κ κ' : Cardinal.{u}}

/-- 既存の affine 係数変更は prism の射である。 -/
def affineEnvelopeCoefficientHom (U : AffineEnvelopeTerm P r n κ)
    (V : AffineEnvelopeTerm P' r n κ') : OrientedPrism.Hom U.X.Q V.X.Q :=
  ⟨affineEnvelopeCoefficientMap f U V, (affineEnvelopeCoefficientMap_spec f U V).1, by
    rw [U.envelope.ideal_eq, Ideal.span_singleton_le_iff_mem]
    change ((affineEnvelopeCoefficientMap f U V).comp
      (U.η.comp (completedFreeDeltaBase P _))) P.generator ∈ V.X.Q.ideal
    rw [U.base_eq, (affineEnvelopeCoefficientMap_spec f U V).2.1]
    exact (V.X.toHom.comp f).map_generator_mem⟩

variable (P P') (hP : IsBoundedPrism P) (hP' : IsBoundedPrism P')
variable (r n : ℕ) (κ κ' : Cardinal.{u})
variable (hκ : cutoff A (prismPolynomialCompletion P (Fin r)) ≤ κ)
variable (hκ' : cutoff B (prismPolynomialCompletion P' (Fin r)) ≤ κ')
local notation "U" => affineEnvelopeTerm P hP r n κ hκ
local notation "V" => affineEnvelopeTerm P' hP' r n κ' hκ'

/-- 概要：affine Čech–Alexander の底変換は両脚を保つ prism の同型。
方針：既存の環比較を δ 射へ持ち上げ、正則な左生成元で prism を作る。
規約：BS 著者版 Remark 4.19。使われ方：drafts の cechAlexanderAffine_baseChange の古典的な型。 -/
theorem cechAlexanderAffine_baseChange :
    letI := f.toRingHom.toAlgebra
    letI := (U).X.toHom.toRingHom.toAlgebra
    let C := PrismCompletedTensor (A := A) (C := (U).X.B) P'
    let l := prismCompletedTensorLeft (A := A) (C := (U).X.B) P'
    let v := prismCompletedTensorRight (A := A) (C := (U).X.B) P'
    ∃ (Qbc : OrientedPrism p C) (e : C ≃+* (V).X.B)
      (g : OrientedPrism.Hom (U).X.Q (V).X.Q),
      P'.deltaStructure.IsDeltaHom Qbc.deltaStructure l ∧
      (U).X.Q.deltaStructure.IsDeltaHom Qbc.deltaStructure v ∧
      Qbc.deltaStructure.IsDeltaHom (V).X.Q.deltaStructure e.toRingHom ∧
      Qbc.ideal.map e.toRingHom = (V).X.Q.ideal ∧
      e.toRingHom.comp l = (V).X.toHom.toRingHom ∧
      e.toRingHom.comp v = g.toRingHom ∧
      g.comp (U).X.toHom = (V).X.toHom.comp f ∧
      ∀ j i, g.toRingHom ((U).η (affineVariable P r n j i)) =
        (V).η (affineVariable P' r n j i) := by
  let := f.toRingHom.toAlgebra
  let := (U).X.toHom.toRingHom.toAlgebra
  let C := PrismCompletedTensor (A := A) (C := (U).X.B) P'
  let l : B →+* C := prismCompletedTensorLeft P'
  let v : (U).X.B →+* C := prismCompletedTensorRight P'
  let D := prismCompletedTensorDelta P' P.deltaStructure (U).X.Q.deltaStructure
    f.map_delta (U).X.toHom.map_delta
  have hL := prismCompletedTensorLeft_isDeltaHom P' P.deltaStructure (U).X.Q.deltaStructure
    f.map_delta (U).X.toHom.map_delta
  have hV := prismCompletedTensorRight_isDeltaHom P' P.deltaStructure (U).X.Q.deltaStructure
    f.map_delta (U).X.toHom.map_delta
  obtain ⟨e, hr, hl⟩ := exists_affineEnvelopeCoefficientBaseChange_equiv
    P P' f hP hP' r n κ κ' hκ hκ'
  have hδ : D.IsDeltaHom (V).X.Q.deltaStructure e.toRingHom := by
    apply prismCompletedTensor_isDeltaHom_of_legs P' P.deltaStructure (U).X.Q.deltaStructure
      f.map_delta (U).X.toHom.map_delta (V).X.Q.deltaStructure e.toRingHom
    · rw [hl]
      exact (V).X.toHom.map_delta
    · rw [hr]
      exact (affineEnvelopeCoefficientMap_spec f U V).1
    · exact (V).X.Q.complete_p
    · change IsModuleComplete (V).X.B ((e.toRingHom.comp l) P'.generator) _
      rw [hl]
      exact (V).X.toHom.isModuleComplete_map_generator
  have hreg : Function.Injective (fun x : C => l P'.generator * x) := by
    intro x y h
    apply e.injective
    apply (V).X.toHom.map_generator_mul_injective
    have he := congrArg e h
    simpa only [map_mul, show e (l P'.generator) = (V).X.toHom.toRingHom P'.generator
      from RingHom.congr_fun hl _] using he
  let Qbc : OrientedPrism p C := OrientedPrism.ofDistinguished D (l P'.generator)
    (hL.map_isDistinguished P'.isDistinguished_generator) hreg
    (prismCompletedTensor_complete_p P') (prismCompletedTensor_complete_generator P')
  let g := affineEnvelopeCoefficientHom f U V
  refine ⟨Qbc, e, g, hL, hV, hδ, ?_, hl, hr, ?_, ?_⟩
  · change (Ideal.span {l P'.generator}).map e.toRingHom = _
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {(e.toRingHom.comp l) P'.generator} = _
    rw [hl]
    exact (V).X.toHom.span_map_generator
  · exact OrientedPrism.Hom.ext (affineEnvelopeCoefficientMap_spec f U V).2.1
  · exact (affineEnvelopeCoefficientMap_spec f U V).2.2

end SerrePositivity.BhattScholze.Prismatic

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Rem 4.19" (partial := component) "BS-W17 H4（11-11）：affine の小さい模型、底変換との項ごとの両立（δ 同型・脚・座標、全単体射に自然）は本体。「Δ を計算する」主張と Tot の底変換は G10 の後。項ごとの導来底変換の同型も本体（AffineEnvelopeDerivedBaseChange） ／ 11-12 夜更新（§4 の見直し）"] _root_.SerrePositivity.BhattScholze.Prismatic.cechAlexanderAffine_baseChange
