module

public import SerrePositivity.InfinityCategories.F2.Ind.ConeTensorCorner
public import SerrePositivity.InfinityCategories.F2.Ind.TensorRightPoint

/-!
概要：元の下方余錐点で試験族を固定し、元の補間領域への実包含を構成する。
方針：元の旧族側の積を経由し、元の pushout の包含で送る。
規約：元の試験族の全係数と同じ指定余錐点を保持する。
使われ方：元の極大点評価の指定変換を scalar comma の相対余錐へ付加する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：元の下方余錐点で固定した試験族の、元の補間領域への包含。
方針：元の積と pushout。規約：元の全射。使われ方：指定変換を付加する相対余錐。 -/
def coneTensorTargetInclusion (A L : SSet.{u}) : A ⟶ coneTensorCorner A L :=
  tensorRightPoint A (joinInr L (Δ[0] : SSet.{u})) ≫
    pushout.inl (A ◁ joinInl L (Δ[0] : SSet.{u})) (joinInl A Δ[0] ▷ L)
/-- 概要：元の包含の全余錐積への像は、同じ元の終点面の旧族包含。
方針：元の全境界と点固定の自然性。規約：全射の等号。使われ方：終点面の回収。 -/
lemma coneTensorTargetInclusion_comp (A L : SSet.{u}) :
    coneTensorTargetInclusion A L ≫ coneTensorCornerInclusion A L =
    joinInl A (Δ[0] : SSet.{u}) ≫ tensorRightPoint (join A Δ[0]) (joinInr L Δ[0]) := by
  rw [coneTensorTargetInclusion, Category.assoc, coneTensorCornerInclusion_old]
  exact (tensorRightPoint_naturality (joinInl A (Δ[0] : SSet.{u})) (joinInr L Δ[0])).symm
/-- 概要：元の終点面の補間領域への包含は単射。
方針：元の余錐積への像で反映する。規約：元の包含。使われ方：指定変換を付加する領域。 -/
instance coneTensorTargetInclusion_mono (A L : SSet.{u}) :
    Mono (coneTensorTargetInclusion A L) :=
  mono_of_mono_fac (coneTensorTargetInclusion_comp A L)
end SerrePositivity.InfinityCategories.F2.Ind
