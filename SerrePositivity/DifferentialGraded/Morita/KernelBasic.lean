module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleLocal
public import SerrePositivity.DifferentialGraded.Module.FunctorExtension

/-! # Morita kernelの向きと主導来合成

## 概要
DからEの右加群導来圏への作用を表すkernelを、右E・左Dの導来bimoduleとして固定する。

## 方針
主bimodule局所化とU12e-localの既存合成を使い、新しい局所化型を作らない。

## 規約と注意
係数は任意可換環。対象宇宙は独立、Small.{u}を明示する。
合成は元の始域DのlocalHomKFlatだけを要求する。一般dg圏の分解をimportしない。

## 使われ方
U16aの作用・随伴・合成と、U16bのgraph比較から利用する。
受入範囲は`formalization-plans/dg-theory-m5-status.md`を参照。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory BimoduleTensor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

/-- D→Eのkernel。右E・左Dなので、bimoduleの添字はE・Dの順になる。 -/
abbrev Kernel := DerivedBimoduleCategory A E D

/-- 恒等作用のkernelは対角bimoduleの主導来像。局所Hom条件は不要。 -/
def kernelIdentity : Kernel A D D :=
  (bimoduleToDerived A D D).obj (BimoduleCategory.of A D D (Bimodule.diagonal A D))

/-- dg関手の延長を表すgraphの主導来像。値はHom_E(e,Fd)。 -/
def kernelGraph (F : DGFunctor A D E) : Kernel A D E :=
  (bimoduleToDerived A E D).obj (BimoduleCategory.of A E D (functorGraph A D E F))

variable (F : Type z) [DGCategory A F] [Small.{u} F]

/-- D→E、E→Fの順に適用するkernel合成。既存合成の出力側はDなのでhDのみを要求する。 -/
def kernelCompose (hD : localHomKFlat A D) (P : Kernel A D E) (Q : Kernel A E F) :
    Kernel A D F :=
  ((derivedBimoduleComposeFunctor A F E D hD).obj P).obj Q

/-- 両kernelの射による合成の射。既存curried主導来関手の作用を使う。 -/
def kernelComposeMap (hD : localHomKFlat A D)
    {P P' : Kernel A D E} {Q Q' : Kernel A E F} (f : P ⟶ P') (g : Q ⟶ Q') :
    kernelCompose A D E F hD P Q ⟶ kernelCompose A D E F hD P' Q' :=
  ((derivedBimoduleComposeFunctor A F E D hD).map f).app Q ≫
    ((derivedBimoduleComposeFunctor A F E D hD).obj P').map g

end SerrePositivity.DifferentialGraded.Morita
