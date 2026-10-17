module
public import SerrePositivity.DifferentialGraded.Tensor.QuasiIsoLeft
public import SerrePositivity.DifferentialGraded.Tensor.Semifree
public import SerrePositivity.DifferentialGraded.Module.LeftQuasiIsoInverse

/-! # opposite上の相対K-flat性による左加群のK-flat解像度

## 概要
opposite上の相対K-flat性による左加群のK-flat解像度。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Tensor/KFlatComparison.lean。局所導来合成の計算部品、一般Morita・
相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 左加群の相対K-flat性を、opposite上の右加群の条件として固定する。 -/
def leftModuleRelativeKFlat (L : LeftModule A D) : Prop :=
  moduleRelativeKFlat A Dᵒᵖ L.toRightOpposite

/-- 左K-flatな因子とのtensorは、右変数の任意の準同型を保存する。 -/
lemma leftModuleRelativeKFlat_preserves_rightQuasiIso (L : LeftModule A D)
    (hL : leftModuleRelativeKFlat A D L) {M N : ModuleCategory A D} (f : M ⟶ N)
    (hf : moduleQuasiIso A D f) :
    QuasiIso ((BalancedTensor.rightTensorFunctor A D L).map f) := by
  have hc := (moduleQuasiIso_iff_acyclic_cone A D f).1 hf
  have hleft : leftModuleAcyclic A Dᵒᵖ
      (ForgetEnrichment.to (Complex A) (moduleCone A D f)).toFunctor :=
    fun x => hc x.unop
  have ht := hL (ForgetEnrichment.to (Complex A) (moduleCone A D f)).toFunctor hleft
  have ho := cochainAcyclic_of_iso ht
    (BalancedTensor.swapIso A D (ForgetEnrichment.to (Complex A) (moduleCone A D f)) L).symm
  exact (complex_quasiIso_iff_acyclic_cone A _).2
    (cochainAcyclic_of_iso ho (BalancedTensor.rightTensorConeIso A D L f).symm)

/-- 任意の左加群に対し、右側のcell解像度を既存左右同値で移送する。 -/
theorem exists_leftRelativeKFlat_resolution (N : LeftModuleCategory A D) :
    ∃ (L : LeftModuleCategory A D) (q : L ⟶ N),
      leftModuleRelativeKFlat A D (ForgetEnrichment.to (Complex A) L) ∧
        leftModuleQuasiIso A D q := by
  let E := leftRightOppositeEquivalence A D
  obtain ⟨P, q, _, hP, _, hq⟩ := exists_relativeKFlat_resolution A Dᵒᵖ (E.functor.obj N)
  refine ⟨E.inverse.obj P, E.inverse.map q ≫ (E.unitIso.app N).inv, ?_, ?_⟩
  · exact moduleRelativeKFlat_of_iso A Dᵒᵖ (E.counitIso.app P) hP
  · exact (leftModuleQuasiIso A D).comp_mem _ _
      ((leftRightOpposite_inverse_quasiIso_iff A D q).2 hq)
      ((leftModuleQuasiIso A D).of_isIso _)

end SerrePositivity.DifferentialGraded
