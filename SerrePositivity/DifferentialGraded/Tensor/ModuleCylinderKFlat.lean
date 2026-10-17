module
public import SerrePositivity.DifferentialGraded.Tensor.TensorModuleIso
public import SerrePositivity.DifferentialGraded.Tensor.KFlatComplex
public import SerrePositivity.DifferentialGraded.Module.Cylinder

/-! # K-flat複体とのtensorとdg加群cylinderの相対K-flat性

## 概要
K-flat複体とのtensorとdg加群cylinderの相対K-flat性。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Bimodule/CylinderKFlat.lean。局所導来合成の計算部品、一般Morita・
相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A]

lemma complexKFlat_interval : complexKFlat A (dgInterval A) := by
  intro L hL
  exact cochainAcyclic_of_homotopyEquiv (complexKFlat_unit A L hL)
    (tensorIntervalHomotopyEquiv A L).symm

variable (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleRelativeKFlat_tensor (K : Complex A) (hK : complexKFlat A K)
    (M : RightModule A D) (hM : moduleRelativeKFlat A D M) :
    moduleRelativeKFlat A D (tensorModule K M) := by
  intro N hN
  exact cochainAcyclic_of_iso (hK _ (hM N hN)) (BalancedTensor.tensorModuleIso A D K M N).symm

lemma modulePrecylinder_relativeKFlat (M : ModuleCategory A D)
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M)) :
    moduleRelativeKFlat A D
      (ForgetEnrichment.to (Complex A) (modulePrecylinder A D M).I) :=
  moduleRelativeKFlat_tensor A D (dgInterval A) (complexKFlat_interval A) _ hM

end SerrePositivity.DifferentialGraded
