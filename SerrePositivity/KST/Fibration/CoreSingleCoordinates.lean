module
public import SerrePositivity.KST.Fibration.RelativeSKernelSquare
public import SerrePositivity.KST.SConstruction.SingleRealizationAdditivity
public import SerrePositivity.KST.SConstruction.StableMultiRealizationAction

/-! # 元の core S 実現と一回の反復実現の座標・元の完全射の一致 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 一回の反復実現は、元の core S 実現と全単体・全作用素で同じ実対象。 -/
theorem coreSingleRealization_obj_eq (X : StableModel.{u}) :
    coreSRealizationFunctor.obj X = (multiRealizationFunctor 1).obj X := by
  apply CategoryTheory.Functor.ext (fun _ => rfl)

/-- 同じ元の完全関手の core S 実現射は、既存の通常の実現関手の射である。 -/
theorem coreSExactMap_realization_eq {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) :
    simplicialDiagonalFunctor.map (coreSExactMap f) =
      coreSRealizationFunctor.map (stableExactInputMap f) := rfl

/-- 単回の座標同型は、同じ実対象の座標の等号による射そのものである。 -/
theorem coreSingleRealizationIso_hom_eq (X : StableModel.{u}) :
    (coreSingleRealizationIso X).hom = eqToHom (coreSingleRealization_obj_eq X) := by
  apply NatTrans.ext
  funext n
  simp only [eqToHom_app]
  rfl

end SerrePositivity.KST.Fibration
