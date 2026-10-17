module
public import SerrePositivity.DifferentialGraded.Morita.AdjunctionKernelCoproducts

/-! # 右随伴を使わないMorita拡張の余積保存

既存のtensor計算による余積保存を使う。一般導来右随伴・unit/counitは使わない。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

/-- 任意の主導来kernelの実際の作用はu-small余積を保存する。 -/
lemma criterionDerivedKernelPreservesCoproducts (K : Kernel A D E)
    (J : Type z) [Small.{u} J] :
    PreservesColimitsOfShape (Discrete J) (kernelDerivedTensor A D E K) :=
  kernelDerivedTensorPreservesCoproducts A D E K

/-- 余積を保存する関手の本質的像は、離散余積で閉じる。充満忠実性は不要。 -/
lemma criterionDerivedEssImage_coproduct
    (T : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    {J : Type z} [Small.{u} J] [PreservesColimitsOfShape (Discrete J) T]
    (F : J → DerivedModuleCategory A E) (hF : ∀ j, T.essImage (F j)) :
    T.essImage (∐ F) := by
  classical
  let X : J → DerivedModuleCategory A D := fun j => (hF j).choose
  let e (j : J) : T.obj (X j) ≅ F j := (hF j).choose_spec.some
  exact ⟨∐ X, ⟨PreservesCoproduct.iso T X ≪≫ Sigma.mapIso e⟩⟩

/-- 主導来kernel作用の本質的像の余積閉性。 -/
lemma criterionDerivedKernelEssImage_coproduct (K : Kernel A D E)
    {J : Type z} [Small.{u} J] (F : J → DerivedModuleCategory A E)
    (hF : ∀ j, (kernelDerivedTensor A D E K).essImage (F j)) :
    (kernelDerivedTensor A D E K).essImage (∐ F) := by
  let := criterionDerivedKernelPreservesCoproducts A D E K J
  exact criterionDerivedEssImage_coproduct A D E _ F hF

end SerrePositivity.DifferentialGraded.Morita
