module
public import SerrePositivity.DifferentialGraded.Morita.Adjunction.Coherence

public import Mathlib.Data.ZMod.Basic

/-! # 実際のMorita右随伴の正方形の監査

## 概要
三条件Morita判定から供給した同値性で、実際の右随伴正方形を使えることを検査する。

## 方針
係数環・対象宇宙を独立に取り、恒等正方形を標数2でも検査する。

## 規約と注意
係数変更前後のMorita性と、左作用比較のモデル条件は消去しない。

## 使われ方
U16cの実際の右随伴をU16dの係数変更へ接続する再現入口。
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.Morita
universe u u' v w v' w'
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (A' : Type u') [CommRing A']
  (D' : Type v') [DGCategory A' D'] [Small.{u'} D']
  (E' : Type w') [DGCategory A' E'] [Small.{u'} E']
  (K : Kernel A D E) (K' : Kernel A' D' E')
  (S : DerivedModuleCategory A D ⥤ DerivedModuleCategory A' D')
  (T : DerivedModuleCategory A E ⥤ DerivedModuleCategory A' E')
  (e : kernelDerivedTensor A D E K ⋙ T ≅ S ⋙ kernelDerivedTensor A' D' E' K')

example (hK : CriterionPerfConditions A D E K) (hK' : CriterionPerfConditions A' D' E' K')
    (hD : CriterionDerivedCompactGeneration A D (moduleCompactGenerators A D))
    (hE : CriterionDerivedCompactGeneration A E (moduleCompactGenerators A E))
    (hD' : CriterionDerivedCompactGeneration A' D' (moduleCompactGenerators A' D'))
    (hE' : CriterionDerivedCompactGeneration A' E' (moduleCompactGenerators A' E')) :
    kernelDerivedHom A D E K ⋙ S ≅ T ⋙ kernelDerivedHom A' D' E' K' := by
  let := criterionDerivedKernelIsEquivalenceOfMoritaConditions A D E K hK
    (moduleCompactGenerators A D) hD (moduleCompactGenerators A E) hE
  let := criterionDerivedKernelIsEquivalenceOfMoritaConditions A' D' E' K' hK'
    (moduleCompactGenerators A' D') hD' (moduleCompactGenerators A' E') hE'
  exact kernelRightAdjointSquareIso A D E A' D' E' K K' S T e

example (D : Type v) [DGCategory (ZMod 2) D] [Small.{0} D]
    (E : Type w) [DGCategory (ZMod 2) E] [Small.{0} E] (K : Kernel (ZMod 2) D E)
    [(kernelDerivedTensor (ZMod 2) D E K).IsEquivalence] :
    kernelRightAdjointSquareIso (ZMod 2) D E (ZMod 2) D E K K (𝟭 _) (𝟭 _)
        (rightUnitor (kernelDerivedTensor (ZMod 2) D E K) ≪≫
          (leftUnitor (kernelDerivedTensor (ZMod 2) D E K)).symm) =
      rightUnitor (kernelDerivedHom (ZMod 2) D E K) ≪≫
        (leftUnitor (kernelDerivedHom (ZMod 2) D E K)).symm :=
  kernelRightAdjointSquareIso_identity (ZMod 2) D E K

#check kernelRightAdjointLocalizedBaseChangeIso
#print axioms kernelRightAdjointSquareIso
#print axioms kernelRightAdjointSquareIso_hom_app
#print axioms kernelRightAdjointSquareIso_counit
#print axioms kernelRightAdjointSquareIso_unit
#print axioms kernelRightAdjointSquareIso_identity
#print axioms kernelRightAdjointLocalizedBaseChangeIso
#print axioms kernelRightAdjointLocalizedBaseChangeIso_counit
