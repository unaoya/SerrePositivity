module
public import SerrePositivity.KST.SConstruction.DGModuleExtensionParameter

/-! # 実延長の全パラメータ作用の値と斉次元
概要：K パラメータの実 tensor 作用を元の coend 生成元で計算する。
方針：第一変数の実パラメータ作用を評価し、パラメータが加群を横切る符号を保持する。
規約：零次元・閉零射に制限しない。使われ方：高次入力の合成・単位の検証。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite HomologicalComplex SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]

/-- 元の実延長の値への、同じパラメータ付き tensor chain map。 -/
def dgModuleExtensionParameterValue {K : Complex A} {F G : DGFunctor A D E}
    (τ : DGFunctorParamTrans A D E K F G) (M : RightModule A D) (e : E) :
    K ⊗ ((dgModuleExtension A D E F).obj M).obj (op e) ⟶
      ((dgModuleExtension A D E G).obj M).obj (op e) :=
  BimoduleTensor.firstParamValue A E D (RightModule A D) (DGFunctor.id (RightModule A D))
    (dgFunctorGraphParameter A D E τ) e M

/-- 同じ元の値の作用を curry すると、全 Hom 自然変換の評価成分になる。 -/
lemma dgModuleExtensionParameterValue_curry {K : Complex A} {F G : DGFunctor A D E}
    (τ : DGFunctorParamTrans A D E K F G) (M : RightModule A D) (e : E) :
    curryRight (dgModuleExtensionParameterValue A D E τ M e) =
      (dgModuleExtensionParameter A D E τ).app M ≫
        moduleHomπ A E ((dgModuleExtension A D E F).obj M)
          ((dgModuleExtension A D E G).obj M) e :=
  (dgModuleExtensionParameter_π A D E τ M e).symm

/-- 元の coend 生成元への作用は、K と加群の次数の交差符号を保持する。 -/
lemma dgModuleExtensionParameterValue_element {K : Complex A} {F G : DGFunctor A D E}
    (τ : DGFunctorParamTrans A D E K F G) (M : RightModule A D) (e : E) (d : D)
    {k r s n : ℤ} (t : K.X k) (m : (M.obj (op d)).X r)
    (x : ((functorGraph A D E F).value e d).X s) (hn : k + (r + s) = n) :
    (dgModuleExtensionParameterValue A D E τ M e).f n
      (ιTensorObj K (((dgModuleExtension A D E F).obj M).obj (op e)) k (r + s) n hn
        (t ⊗ₜ[A] BalancedTensor.element A D M ((functorGraph A D E F).leftAt e) d m x rfl)) =
      (k * r).negOnePow • BalancedTensor.element A D M ((functorGraph A D E G).leftAt e) d m
        ((((Bimodule.paramValue A E D (dgFunctorGraphParameter A D E τ) e d).f k t).v s
          (k + s) (by omega)) x) (by omega) :=
  BimoduleTensor.firstParamValue_element A E D (RightModule A D)
    (DGFunctor.id (RightModule A D)) (dgFunctorGraphParameter A D E τ) e d M t m x hn

end SerrePositivity.KST.SConstruction
