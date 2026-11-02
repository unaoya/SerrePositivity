module
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorHomPrecomposition
public import SerrePositivity.KST.SConstruction.DGParameterPullback
public import SerrePositivity.DifferentialGraded.Tensor.Parameter

/-! # 左加群の任意パラメータの既存 Hom 表示
概要：任意 K の左加群自然変換を、元の左加群 Hom 複体への射として表示する。
方針：二重反対圏への制限と既存の右加群 Hom の普遍性を使う。
規約：左加群の既存の全 Hom を保持する。使われ方：実 tensor の単位・合成保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Opposite SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  {N N' : LeftModule A D}

/-- 元の左加群 Hom 複体への、同じ K 自然変換の表示射。 -/
def dgLeftModuleParameterHom {K : Complex A}
    (τ : DGFunctorParamTrans A D (Complex A) K N N') : K ⟶ leftModuleHom A D N N' :=
  (moduleHomEquiv A Dᵒᵖ K N.toRightOpposite N'.toRightOpposite).symm
    (dgFunctorParamPre A D (Complex A) Dᵒᵖᵒᵖ (dgDoubleUnop A D) τ)

/-- 表示射の元の各対象評価は、入力した同じパラメータ成分。 -/
lemma dgLeftModuleParameterHom_π {K : Complex A}
    (τ : DGFunctorParamTrans A D (Complex A) K N N') (d : D) :
    dgLeftModuleParameterHom A D τ ≫ leftModuleHomπ A D N N' d = τ.app d :=
  moduleHomEquiv_symm_π A Dᵒᵖ K N.toRightOpposite N'.toRightOpposite
    (dgFunctorParamPre A D (Complex A) Dᵒᵖᵒᵖ (dgDoubleUnop A D) τ) (op d)

/-- 既存の左加群 Hom の全評価族からなる普遍パラメータ自然変換。 -/
def dgLeftModuleParameterUniversal :
    DGFunctorParamTrans A D (Complex A) (leftModuleHom A D N N') N N' where
  app := leftModuleHomπ A D N N'
  naturality := leftModuleHomπ_naturality A D N N'

/-- 任意 K の左加群自然変換は、既存の Hom の普遍族の同じ引き戻しである。 -/
lemma dgLeftModuleParameter_factorization {K : Complex A}
    (τ : DGFunctorParamTrans A D (Complex A) K N N') :
    dgParameterPullback A (dgLeftModuleParameterHom A D τ)
        (dgLeftModuleParameterUniversal A D (N := N) (N' := N')) = τ := by
  apply GradedNatTrans.ext
  funext d
  exact dgLeftModuleParameterHom_π A D τ d

end SerrePositivity.KST.SConstruction
