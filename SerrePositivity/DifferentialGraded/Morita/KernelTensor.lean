module
public import SerrePositivity.DifferentialGraded.Morita.KernelBasic

/-! # 任意の指定bimoduleによる通常の加群tensor作用

## 概要
右E・左Dのkernelを右D加群にtensorして右E加群を得るdg関手。

## 方針
既存bimodule合成の後因子を右D加群圏の恒等dg関手として評価する。

## 規約と注意
全加群型のsmallnessやHomのK-flat性は要求しない。dg圏D・EのSmall.{u}のみ明示する。
これはunderived作用であり、任意kernelとのtensorが準同型を保存するとは主張しない。

## 使われ方
U16aの入力加群のsemifree解像度による導来作用と、U16bのgraph延長比較に使う。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Opposite
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

/-- 任意kernel Pによる通常の右加群作用。入力加群を導来化する前のdg関手。 -/
def kernelTensor (P : Bimodule A E D) : DGFunctor A (RightModule A D) (RightModule A E) :=
  (BimoduleTensor.compose A E D (RightModule A D) P
    (DGFunctor.id (RightModule A D))).toFunctor

/-- tensor作用の値は既存balanced tensor。右D加群とkernelの左D評価をこの順で使う。 -/
lemma kernelTensor_value (P : Bimodule A E D) (M : RightModule A D) (e : E) :
    ((kernelTensor A D E P).obj M).obj (op e) =
      BalancedTensor.obj A D M (P.leftAt e) := rfl

/-- graph kernelの場合は既存のdg加群延長そのもの。公開関手を別モデルへ置き換えない。 -/
lemma kernelTensor_graph (F : DGFunctor A D E) :
    kernelTensor A D E (functorGraph A D E F) = dgModuleExtension A D E F := rfl

end SerrePositivity.DifferentialGraded.Morita
