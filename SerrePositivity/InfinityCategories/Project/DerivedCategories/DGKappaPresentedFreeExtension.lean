module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeLabelOperations
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleExtensionSphereComparison
public import SerrePositivity.DifferentialGraded.Functor.DGClosedIsoConjugation
/-!
概要：ラベル付き κ 未満自由模型に、dg 加群延長の全次数作用を移す。
方針：同じ自由 sphere と余積の比較同型を使い、全 Hom 複体を閉同型で共役する。
規約：KST の共役入口は指示された暫定 import。移動・コピー・編集は行わない。
使われ方：16時間試作の固定 dg 関手に対する実 dg 作用。関手引数の厳密則は別途検証する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
open _root_.SerrePositivity.KST.SConstruction
variable (R : Type u) [CommRing R]
variable (D : Type v) (E : Type w) [DGCategory R D] [DGCategory R E]
  [Small.{u} D] [Small.{u} E] (F : DGFunctor R D E) (κ : Cardinal.{u})

/-- 同じ自由表示への延長と、写したラベルの評価との全加群同型。 -/
def dgKappaPresentedFreeExtensionIso (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject D κ) :
    ForgetEnrichment.of (Complex R)
      ((dgModuleExtension R D E F).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeValue R D κ X)) ≅
    ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeValue R E κ
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeObjectMap R F X)) := by
  letI : PreservesColimitsOfSize.{max u v, max u v} (dgModuleExtension R D E F).onClosed :=
    (dgModuleExtensionRestrictionAdjunction R D E F).leftAdjoint_preservesColimits
  refine PreservesCoproduct.iso (dgModuleExtension R D E F).onClosed
    (fun j : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeCells D X.label =>
      freeSphere R D ((equivShrink D).symm (X.label.2 j.down).1)
        (X.label.2 j.down).2) ≪≫ Sigma.whiskerEquiv
      (Equiv.ulift.trans Equiv.ulift.symm) (fun j => ?_)
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionFreeSphereIso R D E F
    ((equivShrink D).symm (X.label.2 j.down).1) (X.label.2 j.down).2 ≪≫
      eqToIso (congrArg
        (fun e => freeSphere R E e (X.label.2 j.down).2)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeLabelMap_object R F X.label j.down).symm)).symm

/-- 元の延長を、同じラベル評価の全 Hom 作用へ共役する。 -/
def dgKappaPresentedFreeActionEvaluated :
    DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject D κ) (RightModule R E) :=
  dgFunctorClosedConjugate R
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeEvaluation R D κ).comp (dgModuleExtension R D E F))
    (fun X => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeValue R E κ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeObjectMap R F X))
    (dgKappaPresentedFreeExtensionIso R D E F κ)

/-- 固定した dg 関手は、小さい自由表示模型の全 Hom 複体へ作用する。 -/
def dgKappaPresentedFreeAction :
    DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject D κ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject E κ) where
  obj := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeObjectMap R F
  map := (dgKappaPresentedFreeActionEvaluated R D E F κ).map
  map_id := (dgKappaPresentedFreeActionEvaluated R D E F κ).map_id
  map_comp := (dgKappaPresentedFreeActionEvaluated R D E F κ).map_comp

end SerrePositivity.InfinityCategories.Project.DerivedCategories
