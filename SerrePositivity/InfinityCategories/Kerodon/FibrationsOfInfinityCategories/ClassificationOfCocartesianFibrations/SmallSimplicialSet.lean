module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.EnrichedFunctorSmallness
public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex

/-!
概要：各次数で小さい単体集合を小さい宇宙の単体集合で表す。
方針：各次数を Shrink で縮小し、同値により面と退化を移す。
規約：宇宙持ち上げした縮小と元の単体集合との厳密な同型を与える。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な unstraightening を小さい全空間で表す。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：各次数で u に小さい単体集合を宇宙 u に縮小する。
方針：次数ごとの縮小の同値で単体作用を共役する。
規約：X 自身の宇宙は max u v。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、小さい left fibration の全空間。 -/
noncomputable def smallSimplicialSet (X : SSet.{max u v})
    [∀ n, Small.{u} (X.obj n)] : SSet.{u} where
  obj n := Shrink.{u} (X.obj n)
  map {n m} α := ↾fun x ↦ equivShrink (X.obj m) (X.map α ((equivShrink (X.obj n)).symm x))
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro x
    change equivShrink (X.obj n) (X.map (𝟙 n) ((equivShrink (X.obj n)).symm x)) = x
    rw [Functor.map_id_apply, Equiv.apply_symm_apply]
  map_comp {n m k} α β := by
    apply ConcreteCategory.hom_ext
    intro x
    change equivShrink (X.obj k) (X.map (α ≫ β) ((equivShrink (X.obj n)).symm x)) =
      equivShrink (X.obj k) (X.map β ((equivShrink (X.obj m)).symm
        (equivShrink (X.obj m) (X.map α ((equivShrink (X.obj n)).symm x)))))
    rw [Equiv.symm_apply_apply, Functor.map_comp_apply]

/-- 概要：縮小した単体集合を持ち上げると元の単体集合と同型。
方針：各次数で Shrink の同値の逆と順方向を使い、単体作用との可換性を計算する。
規約：ホモトピー同値でなく、単体集合の厳密な同型。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、小さい代表と元の unstraightening の比較。 -/
noncomputable def smallSimplicialSetIso (X : SSet.{max u v})
    [∀ n, Small.{u} (X.obj n)] :
    (SSet.uliftFunctor.{v, u}).obj (smallSimplicialSet X) ≅ X where
  hom :=
    { app n := ↾fun x ↦ (equivShrink (X.obj n)).symm x.down
      naturality {n m} α := by
        apply ConcreteCategory.hom_ext
        intro x
        change (equivShrink (X.obj m)).symm
          (equivShrink (X.obj m) (X.map α ((equivShrink (X.obj n)).symm x.down))) =
            X.map α ((equivShrink (X.obj n)).symm x.down)
        exact Equiv.symm_apply_apply _ _ }
  inv :=
    { app n := ↾fun x ↦ ULift.up (equivShrink (X.obj n) x)
      naturality {n m} α := by
        apply ConcreteCategory.hom_ext
        intro x
        change ULift.up (equivShrink (X.obj m) (X.map α x)) =
          ULift.up (equivShrink (X.obj m) (X.map α
            ((equivShrink (X.obj n)).symm (equivShrink (X.obj n) x))))
        rw [Equiv.symm_apply_apply] }
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    apply ULift.ext
    exact Equiv.apply_symm_apply _ _
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact Equiv.symm_apply_apply _ _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
