module
public import SerrePositivity.DifferentialGraded.Morita.AdjunctionKernelCoproducts
public import SerrePositivity.DifferentialGraded.Morita.AdjunctionBrownSuccessor
public import SerrePositivity.DifferentialGraded.Verdier.KernelActionTriangles

/-! # 実際のkernel作用に対する生成元被覆と関係除去

## 概要
任意の主導来kernelについて、初期被覆と生成元の関係を消す後続操作を構成する。

## 方針
実際の余積保存と既存のshift・三角性を、表現対象の被覆・後続操作へ供給する。

## 規約と注意
局所Hom K-flat性・kernelの列の射影性を追加しない。導来右随伴の存在そのものは後続で証明する。

## 使われ方
U16aの一般右随伴を構成する可算近似列の初期値と後続値に使う。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (K : Kernel A D E)

/-- 任意の主導来kernelの作用に対する実際の初期被覆射。 -/
def kernelBrownSeedMap (Y : DerivedModuleCategory A E) :
    (kernelDerivedTensor A D E K).obj
        (brownSeed A D E (kernelDerivedTensor A D E K) Y) ⟶ Y := by
  let := kernelDerivedTensorPreservesCoproducts A D E
    (J := brownSeedIndex A D E (kernelDerivedTensor A D E K) Y) K
  exact brownSeedMap A D E (kernelDerivedTensor A D E K) Y

/-- 実際のkernel作用の初期被覆は、生成元の像からの全ての射を表す。 -/
lemma kernelBrownSeedMap_generator_surjective (Y : DerivedModuleCategory A E) (p : D × ℤ)
    (f : (kernelDerivedTensor A D E K).obj (moduleCompactGenerators A D p) ⟶ Y) :
    ∃ g : moduleCompactGenerators A D p ⟶
        brownSeed A D E (kernelDerivedTensor A D E K) Y,
      (kernelDerivedTensor A D E K).map g ≫ kernelBrownSeedMap A D E K Y = f := by
  let := kernelDerivedTensorPreservesCoproducts A D E
    (J := brownSeedIndex A D E (kernelDerivedTensor A D E K) Y) K
  exact brownSeedMap_generator_surjective A D E (kernelDerivedTensor A D E K) Y p f

/-- 任意の主導来kernelについて、生成元の全関係を消す後続操作を選ぶ。 -/
def kernelBrownSuccessor {X : DerivedModuleCategory A D} {Y : DerivedModuleCategory A E}
    (r : (kernelDerivedTensor A D E K).obj X ⟶ Y) :
    BrownSuccessor A D E (kernelDerivedTensor A D E K) r := by
  let := mainKernelActionCommShift A D E K
  let := mainKernelActionIsTriangulated A D E K
  let := kernelDerivedTensorPreservesCoproducts A D E
    (J := brownRelationIndex A D E (kernelDerivedTensor A D E K) r) K
  exact brownSuccessor A D E (kernelDerivedTensor A D E K) r

/-- 実際のkernelの後続操作は、元の標的射を延長する。 -/
lemma kernelBrownSuccessor_fac {X : DerivedModuleCategory A D} {Y : DerivedModuleCategory A E}
    (r : (kernelDerivedTensor A D E K).obj X ⟶ Y) :
    (kernelDerivedTensor A D E K).map (kernelBrownSuccessor A D E K r).map ≫
      (kernelBrownSuccessor A D E K r).target = r :=
  (kernelBrownSuccessor A D E K r).fac

/-- 実際のkernelの後続操作は、標的射で零になる生成元からの任意の射を消す。 -/
lemma kernelBrownSuccessor_kills {X : DerivedModuleCategory A D} {Y : DerivedModuleCategory A E}
    (r : (kernelDerivedTensor A D E K).obj X ⟶ Y) (p : D × ℤ)
    (f : moduleCompactGenerators A D p ⟶ X)
    (hf : (kernelDerivedTensor A D E K).map f ≫ r = 0) :
    f ≫ (kernelBrownSuccessor A D E K r).map = 0 :=
  (kernelBrownSuccessor A D E K r).kills p f hf

end SerrePositivity.DifferentialGraded.Morita
