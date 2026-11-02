module

public import SerrePositivity.InfinityCategories.Core.Slice
public import SerrePositivity.InfinityCategories.Core.SliceMap
public import SerrePositivity.InfinityCategories.Core.SliceRestriction
public import SerrePositivity.InfinityCategories.Core.UniverseSSetMaps
public import SerrePositivity.InfinityCategories.Core.UniverseSlices
public import SerrePositivity.InfinityCategories.Core.Idempotent.UniverseSliceProjection

/-!
概要：元の点上の全 slice を持ち上げたものと、持ち上げた同じ点上の全 slice の同型。
方針：標準零単体の二重持ち上げを制限同型で除き、元の射影を厳密に保つ。
規約：元の点の同一性と全次数の射影を保持する。
使われ方：元の局所左 Kan 添字の宇宙比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.HomotopyLimits
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 固定図式の等式による slice の移送は、元の射影を保つ。 -/
lemma idemSliceOverEqIso_projection {K X : SSet.{u}} {p q : K ⟶ X} (h : p = q) :
    (eqToIso (congrArg (fun f : K ⟶ X ↦ sliceOver f) h)).hom ≫ sliceOverProjection q =
      sliceOverProjection p := by
  subst q
  exact Category.id_comp _

/-- 元の点上の全 slice の持ち上げを、持ち上げた同じ点上の全 slice と同定する。 -/
def pointSliceUniverseIso {X : SSet.{u}} (x : X _⦋0⦌) :
    (SSet.uliftFunctor.{v, u}).obj (sliceOver (SSet.yonedaEquiv.symm x)) ≅
      sliceOver ((SSet.yonedaEquiv (X := (SSet.uliftFunctor.{v, u}).obj X)).symm (ULift.up x)) := by
  have := sliceOverRestrict_isIso ((SSet.uliftFunctor.{v, u}).map (SSet.yonedaEquiv.symm x))
    (uliftStdSimplexIso.{u, v} 0).inv
  exact uliftSliceOverIso (SSet.yonedaEquiv.symm x) ≪≫
    asIso (sliceOverRestrict ((SSet.uliftFunctor.{v, u}).map (SSet.yonedaEquiv.symm x))
      (uliftStdSimplexIso 0).inv) ≪≫
    eqToIso (congrArg (fun f : (Δ[0] : SSet.{max u v}) ⟶
      (SSet.uliftFunctor.{v, u}).obj X ↦ sliceOver f) (uliftYonedaMap x))

/-- 元の点上の slice の宇宙同型は、元の点への全射影を厳密に保つ。 -/
lemma pointSliceUniverseIso_projection {X : SSet.{u}} (x : X _⦋0⦌) :
    (pointSliceUniverseIso.{u, v} x).hom ≫
      sliceOverProjection
        ((SSet.yonedaEquiv (X := (SSet.uliftFunctor.{v, u}).obj X)).symm (ULift.up x)) =
    (SSet.uliftFunctor.{v, u}).map (sliceOverProjection (SSet.yonedaEquiv.symm x)) := by
  dsimp only [pointSliceUniverseIso, Iso.trans_hom, asIso_hom]
  rw [Category.assoc, Category.assoc, idemSliceOverEqIso_projection (uliftYonedaMap.{u, v} x),
    idemSliceOverRestrict_projection, idemUniverseSliceOverIso_projection]

end SerrePositivity.InfinityCategories.F2.Idempotent
