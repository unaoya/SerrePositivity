module

public import SerrePositivity.InfinityCategories.F2.Ind.ConePointSliceRelativeComparison

/-!
概要：同じ指定点写像の slice のまま、恒等終点を持つ全余錐の持ち上げを比較する。
方針：元の点の標準持ち上げと right-anodyne 相対比較を、同じ始域境界で制限する。
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
  have h := VertexIso.map (conePointSliceRelativeIso p b hb W hp ht)
    (relativeFunctorPre (sliceOverProjection p) b (joinInl A Δ[0]))
  simpa only [relativeFunctorPre_vertex, conePointSliceLift_old] using h

end SerrePositivity.InfinityCategories.F2.Ind
