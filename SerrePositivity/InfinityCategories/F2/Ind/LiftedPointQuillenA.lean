module

public import SerrePositivity.InfinityCategories.F1B.Cofinality.CofinalOpposite
public import SerrePositivity.InfinityCategories.F1.Joins.CosliceTriangleFiber
public import SerrePositivity.InfinityCategories.F1B.Cofinality.QuillenA
public import SerrePositivity.InfinityCategories.F1.Joins.CosliceRestrictionIso
public import SerrePositivity.InfinityCategories.Core.UniverseLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
/-!
概要：小さい零単体の持ち上げで試験した coslice の弱可縮性から right cofinal 性を得る。
方針：元の点の coslice を図式の同型で移し、同じ実引き戻しの弱可縮性を戻す。
規約：元の全射を保持し、追加の Kan 性を要求しない。
使われ方：Ind の評価の宇宙比較と Quillen A。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：持ち上げた零単体下の実引き戻しが弱可縮なら、元の射は right cofinal。
方針：元の点の coslice を図式の同型で移し、同じ実引き戻しの弱可縮性を戻す。
規約：元の全図式を保持。使われ方：Ind の評価の宇宙比較と Quillen A。 -/
lemma isRightCofinal_of_weaklyContractible_lifted_point_under
    {E B : SSet.{u + 1}} [Quasicategory B] (f : E ⟶ B)
    (hc : ∀ z : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[0] : SSet.{u}) ⟶ B,
      IsWeaklyContractible (pullback (sliceUnderProjection z) f)) :
    IsRightCofinal f := by
  apply isRightCofinal_of_weaklyContractible_coslices
  intro b
  let p := SSet.yonedaEquiv.symm b
  let e := HomotopyLimits.uliftStdSimplexIso.{u, u + 1} 0
  let z := e.hom ≫ p
  let r := sliceUnderRestrict p e.hom
  have hr : r ≫ sliceUnderProjection z = sliceUnderProjection p :=
    sliceUnderRestrict_projection p e.hom
  let m := pullback.map f (sliceUnderProjection p) f (sliceUnderProjection z)
    (𝟙 E) r (𝟙 B) (by simp) (by simpa using hr.symm)
  have : IsIso m := by dsimp only [m, r]; infer_instance
  let s := m ≫ (pullbackSymmetry f (sliceUnderProjection z)).hom
  exact (isRightCofinal_of_isIso s).isWeakHomotopyEquivalence.weaklyContractible_iff.mpr (hc z)
end SerrePositivity.InfinityCategories.F2.Ind
