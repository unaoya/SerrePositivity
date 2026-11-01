module
public import SerrePositivity.DifferentialGraded.Morita.Adjunction.Construction

/-! # kernel右随伴の可算近似列の監査

## 概要
任意可換環と独立対象宇宙で、近似列の全段階の関係消去と標的射の互換性を確認する。

## 方針
実際のkernel作用と自然なcoconeの型を検査し、構成宣言の公理を直接出力する。

## 規約と注意
表現可能性と一般右随伴の存在は未完であり、この検査では受け入れない。

## 使われ方
U16aの初期被覆から可算列までの小単位の再現入口。
-/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.Morita
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (K : Kernel A D E) (Y : DerivedModuleCategory A E)

example (n : ℕ) (p : D × ℤ)
    (f : (kernelDerivedTensor A D E K).obj (moduleCompactGenerators A D p) ⟶ Y) :
    ∃ g : moduleCompactGenerators A D p ⟶ (kernelBrownApproximation A D E K Y n).obj,
      (kernelDerivedTensor A D E K).map g ≫
        (kernelBrownApproximation A D E K Y n).target = f :=
  kernelBrownApproximation_generator_surjective A D E K Y n p f

example (n : ℕ) (p : D × ℤ)
    (f : moduleCompactGenerators A D p ⟶ (kernelBrownApproximation A D E K Y n).obj)
    (hf : (kernelDerivedTensor A D E K).map f ≫
      (kernelBrownApproximation A D E K Y n).target = 0) :
    f ≫ kernelBrownTransition A D E K Y n = 0 :=
  kernelBrownTransition_kills A D E K Y n p f hf

example : Cocone (kernelBrownDiagram A D E K Y ⋙ kernelDerivedTensor A D E K) :=
  kernelBrownTargetCocone A D E K Y

#print axioms KernelBrownApproximation
#print axioms kernelBrownApproximationNext
#print axioms kernelBrownApproximation
#print axioms kernelBrownTransition
#print axioms kernelBrownTransition_fac
#print axioms kernelBrownTransition_kills
#print axioms kernelBrownApproximation_generator_surjective
#print axioms kernelBrownDiagram
#print axioms kernelBrownTargetCocone
#print axioms kernelBrownTargetCocone_ι
