module
public import SerrePositivity.InfinityCategories.Derived.DGKappaPresentedFreeLabelOperations
public import SerrePositivity.InfinityCategories.Derived.DGModuleExtensionSphereComparison
public import SerrePositivity.KST.SConstruction.DGClosedIsoConjugation
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded
open SerrePositivity.KST.SConstruction
variable (R : Type u) [CommRing R]
variable (D : Type v) (E : Type w) [DGCategory R D] [DGCategory R E]
  [Small.{u} D] [Small.{u} E] (F : DGFunctor R D E) (κ : Cardinal.{u})

/-- 同じ自由表示への延長と、写したラベルの評価との全加群同型。 -/
def dgKappaPresentedFreeExtensionIso (X : DGKappaPresentedFreeObject D κ) :
    ForgetEnrichment.of (Complex R)
      ((dgModuleExtension R D E F).obj (dgKappaPresentedFreeValue R D κ X)) ≅
    ForgetEnrichment.of (Complex R) (dgKappaPresentedFreeValue R E κ
      (dgKappaPresentedFreeObjectMap R F X)) := by
  letI : PreservesColimitsOfSize.{max u v, max u v} (dgModuleExtension R D E F).onClosed :=
    (dgModuleExtensionRestrictionAdjunction R D E F).leftAdjoint_preservesColimits
  refine PreservesCoproduct.iso (dgModuleExtension R D E F).onClosed
    (fun j : dgKappaSphereFreeCells D X.label =>
      freeSphere R D ((equivShrink D).symm (X.label.2 j.down).1)
        (X.label.2 j.down).2) ≪≫ Sigma.whiskerEquiv
      (Equiv.ulift.trans Equiv.ulift.symm) (fun j => ?_)
  exact (dgModuleExtensionFreeSphereIso R D E F
    ((equivShrink D).symm (X.label.2 j.down).1) (X.label.2 j.down).2 ≪≫
      eqToIso (congrArg
        (fun e => freeSphere R E e (X.label.2 j.down).2)
        (dgKappaSphereFreeLabelMap_object R F X.label j.down).symm)).symm

/-- 元の延長を、同じラベル評価の全 Hom 作用へ共役する。 -/
def dgKappaPresentedFreeActionEvaluated :
    DGFunctor R (DGKappaPresentedFreeObject D κ) (RightModule R E) :=
  dgFunctorClosedConjugate R
    ((dgKappaPresentedFreeEvaluation R D κ).comp (dgModuleExtension R D E F))
    (fun X => dgKappaPresentedFreeValue R E κ (dgKappaPresentedFreeObjectMap R F X))
    (dgKappaPresentedFreeExtensionIso R D E F κ)

/-- 固定した dg 関手は、小さい自由表示模型の全 Hom 複体へ作用する。 -/
def dgKappaPresentedFreeAction :
    DGFunctor R (DGKappaPresentedFreeObject D κ) (DGKappaPresentedFreeObject E κ) where
  obj := dgKappaPresentedFreeObjectMap R F
  map := (dgKappaPresentedFreeActionEvaluated R D E F κ).map
  map_id := (dgKappaPresentedFreeActionEvaluated R D E F κ).map_id
  map_comp := (dgKappaPresentedFreeActionEvaluated R D E F κ).map_comp

end SerrePositivity.InfinityCategories
