module
public import SerrePositivity.EInfinity.FrameHom.FibrantSourceReducedFirst
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ElementsOppositeUniverseIso

/-!
概要：元の持ち上げた通常のHom要素圏の反対nerveを、同じleft-roofの比較へ送る。
方針：同じ元の係数移送の厳密な同型と、元のresolutionLeftRoofColimitMapを合成する。
規約：弱同値性は元の実射についての既存定理から移す。新しい弱同値の仮定を置かない。
使われ方：元のnative fiberと同じ元の固定始域roofを照合する実際の基準射。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.Reedy
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
variable {C : Type u} [Category.{v} C] [ModelCategory C] {X : C}
  (q : CofibrantResolution (C := C) simplex X) (Y : C)

/-- 同じ元のHom単体の反対要素圏から、元のleft-roof比較へ送る実射。 -/
def liftedResolutionLeftRoofColimitMap :
    nerve (ULiftHom.{max u v}
      ((SSet.uliftFunctor.{max u v,v}).obj ((cosimplicialHom q.obj).obj Y)).Elements)ᵒᵖ ⟶
      SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph
        (weakEquivalences C) X Y :=
  (elementsOppositeUniverseNerveIso.{max u v,v} ((cosimplicialHom q.obj).obj Y)).hom ≫
    resolutionLeftRoofColimitMap q Y

/-- 元の実射の弱同値性を、同じ元の係数移送の厳密な同型で移す。 -/
theorem liftedResolutionLeftRoofColimitMap_isWeakHomotopyEquivalence [IsFibrant Y]
    (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C)
      (trivialFibrations C)) :
    IsWeakHomotopyEquivalence (liftedResolutionLeftRoofColimitMap q Y) := by
  let e := elementsOppositeUniverseNerveIso.{max u v,v} ((cosimplicialHom q.obj).obj Y)
  have he : IsWeakHomotopyEquivalence e.hom :=
    AnodyneWeakDetection.isWeakHomotopyEquivalence _ (by infer_instance)
  exact he.comp (resolutionLeftRoofColimitMap_isWeakHomotopyEquivalence_of_first q Y r cof)
end SerrePositivity.EInfinity.FrameHom
