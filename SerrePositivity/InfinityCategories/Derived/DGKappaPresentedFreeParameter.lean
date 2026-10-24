module
public import SerrePositivity.InfinityCategories.Derived.DGKappaPresentedFreeExtension
public import SerrePositivity.DifferentialGraded.Functor.InducedClosedParameter
public import SerrePositivity.KST.SConstruction.DGModuleExtensionParameter
/-!
概要：κ-small 自由表示の作用へ、入力 dg 関手間の全パラメータ変換を移す。
方針：実加群延長のパラメータ作用と任意ラベル族の一般共役入口を合成する。
規約：S 構成本体に依存しない KST の dg 一般論を読み取り専用で使う。
使われ方：16時間試作の関手 Hom 複体における高次作用と豊穣自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded SerrePositivity.KST.SConstruction
variable (R : Type u) [CommRing R] (D : Type v) (E : Type w)
  [DGCategory R D] [DGCategory R E] [Small.{u} D] [Small.{u} E] (κ : Cardinal.{u})

/-- 入力の任意 K 自然変換は、自由表示の二作用の間でも同じ全次数変換を与える。 -/
def dgKappaPresentedFreeParameter {K : Complex R} {F G : DGFunctor R D E}
    (τ : DGFunctorParamTrans R D E K F G) :
    DGFunctorParamTrans R (DGKappaPresentedFreeObject D κ) (DGKappaPresentedFreeObject E κ) K
      (dgKappaPresentedFreeAction R D E F κ) (dgKappaPresentedFreeAction R D E G κ) :=
  inducedDGFunctorClosedConjugateParameter R
    (dgKappaPresentedFreeValue R D κ) (dgKappaPresentedFreeValue R E κ)
    (dgModuleExtension R D E F) (dgModuleExtension R D E G)
    (dgKappaPresentedFreeObjectMap R F) (dgKappaPresentedFreeObjectMap R G)
    (dgKappaPresentedFreeExtensionIso R D E F κ) (dgKappaPresentedFreeExtensionIso R D E G κ)
    (dgModuleExtensionParameter R D E τ)

/-- 入力の全 Hom 複体から、同じラベルの二作用間の全 Hom への作用。 -/
def dgKappaPresentedFreeInputHom (F G : DGFunctor R D E)
    (X : DGKappaPresentedFreeObject D κ) :
    dgFunctorHom R D E F G ⟶ homObject R (DGKappaPresentedFreeObject E κ)
      ((dgKappaPresentedFreeAction R D E F κ).obj X)
      ((dgKappaPresentedFreeAction R D E G κ).obj X) :=
  (dgKappaPresentedFreeParameter R D E κ
    (dgFunctorHomEquiv R D E (dgFunctorHom R D E F G) F G (𝟙 _))).app X

end SerrePositivity.InfinityCategories
