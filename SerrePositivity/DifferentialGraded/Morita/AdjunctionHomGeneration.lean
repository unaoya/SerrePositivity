module
public import SerrePositivity.DifferentialGraded.Morita.AdjunctionHomClosure

/-! # 生成元のHom比較から全入力の表現可能性へ

## 概要
余積を保つ三角関手と指定射のHom比較が、全shift代表生成元で全単射なら全入力でも全単射。

## 方針
全shiftで比較が全単射となる入力の三角・retract・余積閉性を使い、既存の局所化帰納を適用する。

## 規約と注意
表現可能性の存在を仮定しない。u-small余積保存を明示する。

## 使われ方
U16aの任意kernelのtelescopeから実際の導来右随伴を構成する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits Preadditive Pretriangulated
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (L : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
  [L.CommShift ℤ] [L.IsTriangulated]
  {R : DerivedModuleCategory A D} {Y : DerivedModuleCategory A E} (r : L.obj R ⟶ Y)
  (hL : ∀ J : Type u, PreservesColimitsOfShape (Discrete J) L)
include hL

omit [L.CommShift ℤ] [L.IsTriangulated] in
/-- 全shiftのHom比較の全単射性はu-small余積で閉じる。 -/
lemma brownHomProperty_coproduct (J : Type u) (F : J → DerivedModuleCategory A D)
    (hF : ∀ j, brownHomProperty A D E L r (F j)) :
    brownHomProperty A D E L r (∐ F) := by
  intro n
  let := hL J
  apply brownHomComparison_iso A D E L r (PreservesCoproduct.iso (shiftFunctor _ n) F)
  exact brownHomComparison_coproduct A D E L r (fun j => (F j)⟦n⟧) (fun j => hF j n)

/-- 全shift代表生成元での比較から、全主導来入力でのHom全単射を得る。 -/
lemma brownHomComparison_all
    (hgen : ∀ p : D × ℤ,
      Function.Bijective (brownHomComparison A D E L r (moduleCompactGenerators A D p)))
    (X : DerivedModuleCategory A D) :
    Function.Bijective (brownHomComparison A D E L r X) := by
  let P := brownHomProperty A D E L r
  have hperf : ∀ Z : DerivedModuleCategory A D, modulePerfect A D Z → P Z := by
    apply (modulePerfect_le_iff_generators A D P).2
    intro d n
    exact hgen (d,n)
  have hX : P X := moduleLocalizing_all A D P
    (brownHomProperty_coproduct A D E L r hL) hperf X
  exact brownHomComparison_iso A D E L r ((shiftFunctorZero _ ℤ).app X).symm (hX 0)

omit hL

variable (K : Kernel A D E) (Y' : DerivedModuleCategory A E)
  (S : KernelBrownTelescope A D E K Y')

/-- 任意kernelの実際のtelescopeは、全入力でHomを表現する。 -/
lemma kernelBrownTelescope_hom_bijective (X : DerivedModuleCategory A D) :
    Function.Bijective (fun f : X ⟶ S.obj => (kernelDerivedTensor A D E K).map f ≫ S.target) := by
  let := mainKernelActionCommShift A D E K
  let := mainKernelActionIsTriangulated A D E K
  exact brownHomComparison_all A D E (kernelDerivedTensor A D E K) S.target
    (fun J => kernelDerivedTensorPreservesCoproducts A D E (J := J) K)
    (kernelBrownTelescope_generator_bijective A D E K Y' S) X

/-- 任意kernelのtelescopeの全入力Hom比較を同値に束ねる。 -/
def kernelBrownTelescopeHomEquiv (X : DerivedModuleCategory A D) :
    (X ⟶ S.obj) ≃ ((kernelDerivedTensor A D E K).obj X ⟶ Y') :=
  Equiv.ofBijective _ (kernelBrownTelescope_hom_bijective A D E K Y' S X)

end SerrePositivity.DifferentialGraded.Morita
