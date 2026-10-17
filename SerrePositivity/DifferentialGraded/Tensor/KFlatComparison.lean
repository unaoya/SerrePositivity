module
public import SerrePositivity.DifferentialGraded.Tensor.LeftKFlatResolution
public import SerrePositivity.DifferentialGraded.Tensor.LeftNaturality

/-! # 相対K-flat右加群間の準同型のtensorによる保存

## 概要
相対K-flat右加群間の準同型のtensorによる保存。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Tensor/BimoduleKFlatQuasiIso.lean。局所導来合成の計算部品、
一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 両端の右相対K-flat性があれば、左因子に条件を課さず準同型を保存する。 -/
lemma rightTensor_relativeKFlat_quasiIso (L : LeftModule A D) {M N : ModuleCategory A D}
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M))
    (hN : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) N))
    (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    QuasiIso ((rightTensorFunctor A D L).map f) := by
  obtain ⟨P, q, hP, hq⟩ := exists_leftRelativeKFlat_resolution A D
    (ForgetEnrichment.of (Complex A) L)
  let τ := rightTensorLeftMap A D q
  have htop : QuasiIso
      ((rightTensorFunctor A D (ForgetEnrichment.to (Complex A) P)).map f) :=
    leftModuleRelativeKFlat_preserves_rightQuasiIso A D
      (ForgetEnrichment.to (Complex A) P) hP f hf
  have hleft : QuasiIso (τ.app M) := moduleRelativeKFlat_preserves_leftQuasiIso A D
    (ForgetEnrichment.to (Complex A) M) hM q hq
  have hright : QuasiIso (τ.app N) := moduleRelativeKFlat_preserves_leftQuasiIso A D
    (ForgetEnrichment.to (Complex A) N) hN q hq
  have hcomp : QuasiIso (τ.app M ≫ (rightTensorFunctor A D L).map f) := by
    exact (τ.naturality f) ▸ (quasiIso_comp _ _)
  exact quasiIso_of_comp_left (τ.app M) _

end SerrePositivity.DifferentialGraded.BalancedTensor
