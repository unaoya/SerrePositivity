module

public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.Slice
public import SerrePositivity.InfinityCategories.Core.SliceMap
public import SerrePositivity.InfinityCategories.F1B.KanExtension.PointSliceHomotopy

/-!
分割で生成：docstring を書き直すこと
概要：余錐は元の図式から定値図式への実際のホモトピーを与える。
方針：余錐を頂点の slice の図式とみなし、既存の円柱比較を使う。
規約：余錐の頂点も元の図式も変更しない。
使われ方：filtered ∞ 圏の有限図式の収縮を Kan 置換へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：指定余錐から元の図式をその頂点へ収縮するホモトピーを構成する。
方針：右因子の頂点を固定して slice へ curry し、既存のホモトピーの射影を同定する。
規約：値域の充填性は不要。使われ方：有限図式の指定した収縮。 -/
def coconeNullHomotopy {K C : SSet.{u}} {p : K ⟶ C} (c : JoinCocone p) :
    SSet.Homotopy p (SSet.const c.vertex) := by
  have hp : joinInr K Δ[0] ≫ c.val = SSet.yonedaEquiv.symm c.vertex := by
    rw [c.vertex_eq, Equiv.symm_apply_apply]
  let f := sliceOverCurry c.val hp
  have hf : f ≫ sliceOverProjection (SSet.yonedaEquiv.symm c.vertex) = p := by
    rw [← sliceOverUncurry_projection, sliceOverUncurry_curry]
    exact c.property
  exact Eq.mp (congrArg (fun q : K ⟶ C ↦ SSet.Homotopy q (SSet.const c.vertex)) hf)
    (F1B.kanPointSliceHomotopy c.vertex f)

end SerrePositivity.InfinityCategories.F2
