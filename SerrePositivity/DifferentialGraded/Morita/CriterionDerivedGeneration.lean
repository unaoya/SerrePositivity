module
public import SerrePositivity.DifferentialGraded.Morita.CriterionDerivedCoproducts
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedLocalizingGeneration
public import SerrePositivity.DifferentialGraded.Perfect.CompactConverse

/-! # 明示したcompact生成による本質的像の局所化帰納

生成族の各対象のcompact性と、余積閉三角部分圏による生成を別々に保持する。
充満性を得る前に本質的像の三角閉性を仮定することはしない。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 各生成元のcompact性と、u-small余積・錐・shiftによる全対象の生成。 -/
structure CriterionDerivedCompactGeneration {I : Type z} [Small.{u} I]
    (G : I → DerivedModuleCategory A D) : Prop where
  compact : ∀ i, moduleCompact A D (G i)
  localizing : ∀ (P : ObjectProperty (DerivedModuleCategory A D))
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms],
    (∀ (J : Type u) (F : J → DerivedModuleCategory A D), (∀ j, P (F j)) → P (∐ F)) →
    (∀ i, P (G i)) → ∀ X, P X

variable (E : Type w) [DGCategory A E] [Small.{u} E]
  (T : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
  [T.CommShift ℤ] [T.IsTriangulated] [T.Full]
  (hcop : ∀ J : Type u, PreservesColimitsOfShape (Discrete J) T)

include hcop in
/-- 充満な三角関手の本質的像がcompact生成族を含めば、全対象を含む。
右随伴による像の記述は使わない。 -/
lemma criterionDerivedEssSurj_of_compactGeneration
    {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A E)
    (hG : CriterionDerivedCompactGeneration A E G)
    (himage : ∀ i, T.essImage (G i)) : T.EssSurj := by
  refine ⟨fun X => hG.localizing T.essImage ?_ himage X⟩
  intro J F hF
  let := hcop J
  exact criterionDerivedEssImage_coproduct A D E T F hF

include hcop in
/-- Perf上の本質的全射と明示したcompact生成を、全対象の本質的全射へ拡張する。
三角性・充満性は入力とし、充満忠実性の局所化帰納とは分ける。 -/
lemma criterionDerivedEssSurj_of_perfectImage
    {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A E)
    (hG : CriterionDerivedCompactGeneration A E G)
    (hperf : ∀ Y : DerivedModuleCategory A E, modulePerfect A E Y → T.essImage Y) :
    T.EssSurj :=
  criterionDerivedEssSurj_of_compactGeneration A D E T hcop G hG
    (fun i => hperf _ (moduleCompact_perfect A E (hG.compact i)))

/-- 一般kernelの作用についても、同じ右随伴なしの局所化帰納を使う。 -/
lemma criterionDerivedKernelEssSurj_of_perfectImage (K : Kernel A D E)
    [(kernelDerivedTensor A D E K).CommShift ℤ]
    [(kernelDerivedTensor A D E K).IsTriangulated]
    [(kernelDerivedTensor A D E K).Full]
    {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A E)
    (hG : CriterionDerivedCompactGeneration A E G)
    (hperf : ∀ Y : DerivedModuleCategory A E, modulePerfect A E Y →
      (kernelDerivedTensor A D E K).essImage Y) :
    (kernelDerivedTensor A D E K).EssSurj :=
  criterionDerivedEssSurj_of_perfectImage A D E (kernelDerivedTensor A D E K)
    (fun J => criterionDerivedKernelPreservesCoproducts A D E K J) G hG hperf

end SerrePositivity.DifferentialGraded.Morita
