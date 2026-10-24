module
public import SerrePositivity.InfinityCategories.Derived.DGKappaPresentedSourceAction
public import SerrePositivity.DifferentialGraded.Functor.InducedClosedParameter
public import SerrePositivity.KST.SConstruction.DGModuleExtensionParameter
/-!
概要：出発提示を保持する作用へ dg 関手間の任意パラメータ変換を送る。
方針：既存の延長パラメータ作用を、ラベル族の一般共役入口で移送する。
規約：全次数の変換を保持し、入力関手を離散化しない。
使われ方：16時間試作の関手変数 Hom 複体への豊穣作用の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded SerrePositivity.KST.SConstruction
variable (R : Type u) [CommRing R] (D E : Type u)
  [DGCategory R D] [DGCategory R E] (κ : Cardinal.{u})

def dgKappaPresentedSourceParameter {K : Complex R} {F G : DGFunctor R D E}
    (τ : DGFunctorParamTrans R D E K F G) :
    DGFunctorParamTrans R (DGKappaPresentedSourceObject R D κ)
      (DGKappaPresentedSourceObject R E κ) K
      (dgKappaPresentedSourceAction R D E κ F) (dgKappaPresentedSourceAction R D E κ G) :=
  inducedDGFunctorClosedConjugateParameter R
    (dgKappaPresentedSourceValue R D κ) (dgKappaPresentedSourceValue R E κ)
    (dgModuleExtension R D E F) (dgModuleExtension R D E G)
    (dgKappaPresentedSourceObjectMap R D κ E F) (dgKappaPresentedSourceObjectMap R D κ E G)
    (dgKappaPresentedSourceActionIso R D E κ F) (dgKappaPresentedSourceActionIso R D E κ G)
    (dgModuleExtensionParameter R D E τ)

def dgKappaPresentedSourceInputHom (F G : DGFunctor R D E)
    (X : DGKappaPresentedSourceObject R D κ) :
    dgFunctorHom R D E F G ⟶ homObject R (DGKappaPresentedSourceObject R E κ)
      ((dgKappaPresentedSourceAction R D E κ F).obj X)
      ((dgKappaPresentedSourceAction R D E κ G).obj X) :=
  (dgKappaPresentedSourceParameter R D E κ
    (dgFunctorHomEquiv R D E (dgFunctorHom R D E F G) F G (𝟙 _))).app X

end SerrePositivity.InfinityCategories
