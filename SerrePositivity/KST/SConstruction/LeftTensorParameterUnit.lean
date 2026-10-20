module
public import SerrePositivity.KST.SConstruction.LeftTensorParameterFactorization
public import SerrePositivity.KST.SConstruction.DGFunctorHomIdentity
public import SerrePositivity.DifferentialGraded.Tensor.Enriched

/-! # 任意パラメータ表示からの元の左 tensor 単位保存
概要：入力の単位自然変換は、元の実 tensor の単位を回収する。
方針：既存の左加群 Hom 表示と実 tensor dg 関手の単位法則を使う。
規約：元の左右加群と coend の射を保持する。使われ方：高次 Perf 作用の単位。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Opposite SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 元の左加群の単位自然変換の Hom 表示は、同じ既存の閉単位。 -/
lemma dgLeftModuleParameterHom_identity (N : LeftModule A D) :
    dgLeftModuleParameterHom A D (dgFunctorParamIdentity A D (Complex A) N) =
      moduleIdentity A Dᵒᵖ N.toRightOpposite := by
  apply moduleHom_ext
  intro d
  exact (dgLeftModuleParameterHom_π A D (dgFunctorParamIdentity A D (Complex A) N) d.unop).trans
    (moduleIdentity_π A Dᵒᵖ N.toRightOpposite d).symm

/-- 単位パラメータの作用は、同じ元の coend の閉単位である。 -/
lemma dgLeftParamHom_identity (M : RightModule A D) (N : LeftModule A D) :
    curryRight (BalancedTensor.leftParamMap A D M
        (dgFunctorParamIdentity A D (Complex A) N).app
        (dgFunctorParamIdentity A D (Complex A) N).naturality) =
      identity (BalancedTensor.obj A D M N) := by
  rw [dgLeftParamHom_factorization, dgLeftModuleParameterHom_identity]
  exact (BalancedTensor.leftTensorDG A D M).map_id N

end SerrePositivity.KST.SConstruction
