module

public import SerrePositivity.InfinityCategories.F2.Ind.ConeTerminalSliceComparison

/-!
概要：同じ指定点写像の slice のまま、恒等終点を持つ全余錐の持ち上げを比較する。
方針：指定点を Yoneda 表示に一度戻して、証明済みの相対頂点同型を使う。
規約：元の指定点・底の全図式を保持。使われ方：実補間円柱への直接適用。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 任意の同じ点写像の slice 内で、恒等終点から得られる底を固定した比較。 -/
def conePointSliceBoundaryRelativeIso {A X : SSet.{u}} [Quasicategory X]
    (p : (Δ[0] : SSet.{u}) ⟶ X) (b : join A (Δ[0] : SSet.{u}) ⟶ X)
    (hb : joinInr A Δ[0] ≫ b = p) (W : join A (Δ[0] : SSet.{u}) ⟶ sliceOver p)
    (hp : W ≫ sliceOverProjection p = b)
    (ht : sliceOverUncurry (joinInr A Δ[0] ≫ W) = SSet.const (SSet.yonedaEquiv p)) :
    VertexIso
      (relativeFunctorVertex (sliceOverProjection p) (joinInl A Δ[0] ≫ b)
        (joinInl A Δ[0] ≫ W) (by rw [Category.assoc, hp]))
      (relativeFunctorVertex (sliceOverProjection p) (joinInl A Δ[0] ≫ b)
        (sliceOverCurry b hb) (sliceOverCurry_projection b hb)) := by
  generalize hx : SSet.yonedaEquiv p = x at *
  have he : SSet.yonedaEquiv.symm x = p := by rw [← hx, Equiv.symm_apply_apply]
  cases he
  have htip : joinInr A Δ[0] ≫ W = SSet.yonedaEquiv.symm (sliceIdentityCone x) := by
    apply sliceOverUncurry_injective (SSet.yonedaEquiv.symm x)
    rw [sliceOverUncurry_yoneda]
    change sliceOverUncurry (joinInr A Δ[0] ≫ W) = SSet.const x
    exact ht
  exact coneTerminalSliceBoundaryRelativeIso x b hb W hp htip

end SerrePositivity.InfinityCategories.F2.Ind
