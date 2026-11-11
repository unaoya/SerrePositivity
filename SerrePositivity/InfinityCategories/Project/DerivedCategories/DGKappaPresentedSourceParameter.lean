module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceAction
public import SerrePositivity.DifferentialGraded.Functor.Closed
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded _root_.SerrePositivity.KST.SConstruction
variable (R : Type u) [CommRing R] (D E : Type u)
  [DGCategory R D] [DGCategory R E] (κ : Cardinal.{u})

def dgKappaPresentedSourceParameter {K : Complex R} {F G : DGFunctor R D E}
    (τ : DGFunctorParamTrans R D E K F G) :
    DGFunctorParamTrans R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R D κ)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R E κ) K
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceAction R D E κ F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceAction R D E κ G) :=
  inducedDGFunctorClosedConjugateParameter R
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R D κ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R E κ)
    (dgModuleExtension R D E F) (dgModuleExtension R D E G)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceObjectMap R D κ E F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceObjectMap R D κ E G)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceActionIso R D E κ F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceActionIso R D E κ G)
    (dgModuleExtensionParameter R D E τ)

def dgKappaPresentedSourceInputHom (F G : DGFunctor R D E)
    (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R D κ) :
    dgFunctorHom R D E F G ⟶ homObject R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R E κ)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceAction R D E κ F).obj X)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceAction R D E κ G).obj X) :=
  (dgKappaPresentedSourceParameter R D E κ
    (dgFunctorHomEquiv R D E (dgFunctorHom R D E F G) F G (𝟙 _))).app X

end SerrePositivity.InfinityCategories.Project.DerivedCategories
