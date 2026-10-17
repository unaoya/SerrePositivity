module
public import SerrePositivity.DifferentialGraded.Morita.U16a
public import SerrePositivity.DifferentialGraded.Morita.CriterionDerived
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # U16c：三条件のMorita同値と実際の一般右随伴の統合

## 概要
Perf判定と全導来拡張の同値の逆関手を、U16aの実際の一般右随伴と同定する。
実際のunit/counitの可逆性と、その随伴そのものを使う同値を公開する。

## 方針
他担当の三条件判定・全導来拡張をそのまま再利用し、Mathlibの右随伴の一意性で比較する。

## 規約と注意
三条件と両側compact生成は明示した入力。局所Hom K-flat性・kernel列の射影性は追加しない。
抽象的に同値な別関手ではなく、公開主導来作用と公開unit/counitを比較する。

## 使われ方
U16cの最終統合、U17bのMorita同値の適用、一般右随伴を使う計算。
-/
@[expose] public section
noncomputable section
universe u v w z z'
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (K : Kernel A D E) (hK : CriterionPerfConditions A D E K)
  {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A D)
  (hG : CriterionDerivedCompactGeneration A D G)
  {J : Type z'} [Small.{u} J] (H : J → DerivedModuleCategory A E)
  (hH : CriterionDerivedCompactGeneration A E H)

/-- 他担当の完成した三条件判定と全導来拡張による、実際のkernel作用の同値。 -/
def kernelMoritaEquivalence : DerivedModuleCategory A D ≌ DerivedModuleCategory A E :=
  criterionDerivedKernelEquivalenceOfMoritaConditions A D E K hK G hG H hH

/-- 構成したMorita同値の順方向は主導来作用そのもの。 -/
lemma kernelMoritaEquivalence_functor :
    (kernelMoritaEquivalence A D E K hK G hG H hH).functor = kernelDerivedTensor A D E K := rfl

/-- 一般右随伴は、別担当の全導来Morita同値の逆関手に自然同型である。 -/
def kernelMoritaHomIsoInverse : kernelDerivedHom A D E K ≅
    (kernelMoritaEquivalence A D E K hK G hG H hH).inverse :=
  Adjunction.rightAdjointUniq (kernelDerivedAdjunction A D E K)
    (kernelMoritaEquivalence A D E K hK G hG H hH).toAdjunction

/-- 右随伴の比較は実際の単位を同値の単位へ運ぶ。 -/
lemma kernelMoritaHomIsoInverse_unit :
    kernelDerivedUnit A D E K ≫ Functor.whiskerLeft (kernelDerivedTensor A D E K)
      (kernelMoritaHomIsoInverse A D E K hK G hG H hH).hom =
    (kernelMoritaEquivalence A D E K hK G hG H hH).unitIso.hom :=
  Adjunction.unit_rightAdjointUniq_hom (kernelDerivedAdjunction A D E K)
    (kernelMoritaEquivalence A D E K hK G hG H hH).toAdjunction

/-- 右随伴の比較は同値の余単位を実際の余単位へ運ぶ。 -/
lemma kernelMoritaHomIsoInverse_counit :
    Functor.whiskerRight (kernelMoritaHomIsoInverse A D E K hK G hG H hH).hom
      (kernelDerivedTensor A D E K) ≫
      (kernelMoritaEquivalence A D E K hK G hG H hH).counitIso.hom =
    kernelDerivedCounit A D E K :=
  Adjunction.rightAdjointUniq_hom_counit (kernelDerivedAdjunction A D E K)
    (kernelMoritaEquivalence A D E K hK G hG H hH).toAdjunction

include hK G hG H hH in
/-- 三条件とcompact生成の下で、U16aの実際の単位は自然同型である。 -/
lemma kernelMoritaUnit_isIso : IsIso (kernelDerivedUnit A D E K) := by
  let : (kernelDerivedTensor A D E K).IsEquivalence :=
    criterionDerivedKernelIsEquivalenceOfMoritaConditions A D E K hK G hG H hH
  change IsIso (kernelDerivedAdjunction A D E K).unit
  infer_instance

include hK G hG H hH in
/-- 三条件とcompact生成の下で、U16aの実際の余単位は自然同型である。 -/
lemma kernelMoritaCounit_isIso : IsIso (kernelDerivedCounit A D E K) := by
  let : (kernelDerivedTensor A D E K).IsEquivalence :=
    criterionDerivedKernelIsEquivalenceOfMoritaConditions A D E K hK G hG H hH
  change IsIso (kernelDerivedAdjunction A D E K).counit
  infer_instance

/-- 実際の一般右随伴と実際のunit/counitを持つMorita同値。 -/
def kernelMoritaAdjunctionEquivalence : DerivedModuleCategory A D ≌ DerivedModuleCategory A E := by
  let : IsIso (kernelDerivedAdjunction A D E K).unit :=
    kernelMoritaUnit_isIso A D E K hK G hG H hH
  let : IsIso (kernelDerivedAdjunction A D E K).counit :=
    kernelMoritaCounit_isIso A D E K hK G hG H hH
  let : ∀ X, IsIso ((kernelDerivedAdjunction A D E K).unit.app X) := fun _ => inferInstance
  let : ∀ Y, IsIso ((kernelDerivedAdjunction A D E K).counit.app Y) := fun _ => inferInstance
  exact (kernelDerivedAdjunction A D E K).toEquivalence

/-- 統合同値の順方向は元の主導来作用である。 -/
lemma kernelMoritaAdjunctionEquivalence_functor :
    (kernelMoritaAdjunctionEquivalence A D E K hK G hG H hH).functor =
      kernelDerivedTensor A D E K := rfl

/-- 統合同値の逆方向は構成済みの一般右随伴そのものである。 -/
lemma kernelMoritaAdjunctionEquivalence_inverse :
    (kernelMoritaAdjunctionEquivalence A D E K hK G hG H hH).inverse =
      kernelDerivedHom A D E K := rfl

/-- 統合同値の単位はU16aの実際の単位である。 -/
lemma kernelMoritaAdjunctionEquivalence_unit :
    (kernelMoritaAdjunctionEquivalence A D E K hK G hG H hH).unitIso.hom =
      kernelDerivedUnit A D E K := rfl

/-- 統合同値の余単位はU16aの実際の余単位である。 -/
lemma kernelMoritaAdjunctionEquivalence_counit :
    (kernelMoritaAdjunctionEquivalence A D E K hK G hG H hH).counitIso.hom =
      kernelDerivedCounit A D E K := rfl

end SerrePositivity.DifferentialGraded.Morita
