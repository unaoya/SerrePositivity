module

public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseCosliceProjection

/-!
概要：元の点上の全 coslice を持ち上げたものと、持ち上げた同じ点上の全 coslice の同型。
方針：標準零単体の二重持ち上げを制限同型で除き、元の射影を厳密に保つ。
規約：元の点の同一性と全次数の射影を保持する。
使われ方：元の局所右 Kan 添字の宇宙比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 固定図式の等式による coslice の移送は、元の射影を保つ。 -/
lemma cosliceEqIso_projection {K X : SSet.{u}} {p q : K ⟶ X} (h : p = q) :
    (eqToIso (congrArg (fun f : K ⟶ X ↦ sliceUnder f) h)).hom ≫ sliceUnderProjection q =
      sliceUnderProjection p := by
  subst q
  exact Category.id_comp _

/-- 元の点上の全 coslice の持ち上げを、持ち上げた同じ点上の全 coslice と同定する。 -/
def pointCosliceUniverseIso {X : SSet.{u}} (x : X _⦋0⦌) :
    (SSet.uliftFunctor.{v, u}).obj (sliceUnder (SSet.yonedaEquiv.symm x)) ≅
      sliceUnder ((SSet.yonedaEquiv (X :=
        (SSet.uliftFunctor.{v, u}).obj X)).symm (ULift.up x)) := by
  have := sliceUnderRestrict_isIso ((SSet.uliftFunctor.{v, u}).map (SSet.yonedaEquiv.symm x))
    (uliftStdSimplexIso.{u, v} 0).inv
  exact uliftSliceUnderIso (SSet.yonedaEquiv.symm x) ≪≫
    asIso (sliceUnderRestrict ((SSet.uliftFunctor.{v, u}).map (SSet.yonedaEquiv.symm x))
      (uliftStdSimplexIso 0).inv) ≪≫
    eqToIso (congrArg (fun f : (Δ[0] : SSet.{max u v}) ⟶
      (SSet.uliftFunctor.{v, u}).obj X ↦ sliceUnder f) (uliftYonedaMap x))

/-- 元の点上の coslice の宇宙同型は、元の点への全射影を厳密に保つ。 -/
lemma pointCosliceUniverseIso_projection {X : SSet.{u}} (x : X _⦋0⦌) :
    (pointCosliceUniverseIso.{u, v} x).hom ≫
      sliceUnderProjection
        ((SSet.yonedaEquiv (X := (SSet.uliftFunctor.{v, u}).obj X)).symm (ULift.up x)) =
    (SSet.uliftFunctor.{v, u}).map (sliceUnderProjection (SSet.yonedaEquiv.symm x)) := by
  dsimp only [pointCosliceUniverseIso, Iso.trans_hom, asIso_hom]
  rw [Category.assoc, Category.assoc, cosliceEqIso_projection (uliftYonedaMap.{u, v} x),
    sliceUnderRestrict_projection, uliftSliceUnderIso_projection]

end SerrePositivity.InfinityCategories.HomotopyLimits
