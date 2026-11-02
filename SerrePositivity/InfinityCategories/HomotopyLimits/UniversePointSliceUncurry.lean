module

public import SerrePositivity.InfinityCategories.Core.Idempotent.UniversePointSlice
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseSliceUncurry

/-!
概要：元の指定点の slice の宇宙比較は、その元の全普遍錐の展開も保つ。
方針：固定図式の等式輸送と標準零単体への制限を消去し、元の全錐族の比較へ戻す。
規約：元の点と元の全錐の射を厳密に保持する。
使われ方：元の右 Kan 標準全錐の宇宙持ち上げとの厳密な一致。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の固定図式の等式輸送は、同じ全 slice 錐の展開を変えない。 -/
lemma sliceOverUncurry_eqIso {A K X : SSet.{u}} {p q : K ⟶ X}
    (h : p = q) (f : A ⟶ sliceOver p) :
    sliceOverUncurry (f ≫ (eqToIso (congrArg (fun r : K ⟶ X => sliceOver r) h)).hom) =
      sliceOverUncurry f := by
  subst q
  rw [eqToIso_refl, Iso.refl_hom, Category.comp_id]

/-- 同じ点の slice 宇宙同型は、元の全普遍錐族の展開を厳密に保つ。 -/
lemma pointSliceUniverseIso_uncurry {A X : SSet.{u}} (x : X _⦋0⦌)
    (f : A ⟶ sliceOver (SSet.yonedaEquiv.symm x)) :
    sliceOverUncurry ((SSet.uliftFunctor.{v, u}).map f ≫
      (F2.Idempotent.pointSliceUniverseIso.{u, v} x).hom) =
    (uliftCoconeShapeIso.{u, v} A 0).inv ≫
      (SSet.uliftFunctor.{v, u}).map (sliceOverUncurry f) := by
  dsimp only [F2.Idempotent.pointSliceUniverseIso, Iso.trans_hom, asIso_hom]
  rw [← Category.assoc, ← Category.assoc, sliceOverUncurry_eqIso (uliftYonedaMap.{u, v} x),
    sliceOverUncurry_restrict, sliceOverUncurry_ulift]
  exact (Category.assoc _ _ _).symm

end SerrePositivity.InfinityCategories.HomotopyLimits
