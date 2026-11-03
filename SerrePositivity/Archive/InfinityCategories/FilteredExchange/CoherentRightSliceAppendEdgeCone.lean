module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentRightSliceAppendFaces
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.AppendEdgeConeCoordinates

/-!
概要：元の全右 slice の錐へ指定射を追加し、その同じ実辺上の実錐へ束ねる。
方針：二終点を同じ区間へ再結合し、既存の実固定辺と自然性を使う。
規約：同じ全錐と指定射を保持。使われ方：三射の実高次族の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {Z W : C} (g : Z ⟶ W)
local notation "RZ" => sliceOver (SSet.yonedaEquiv.symm (coherentNerveVertex Z))

/-- 元の全錐と同じ追加射を、実区間を右に持つ全図式として読む。 -/
def coherentRightSliceAppendEdgeCone {n : ℕ} (c : RZ _⦋n⦌) :
    join (Δ[n] : SSet.{max u v}) Δ[1] ⟶ SimplicialNerve C :=
  appendEdgeConeCoordinates Δ[n] ≫ coherentRightSliceAppendCone g c

/-- 同じ実区間への全錐は、元の全添字制限に自然。 -/
lemma coherentRightSliceAppendEdgeCone_naturality {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (c : RZ _⦋n⦌) :
    joinMap (stdSimplex.map α) (𝟙 Δ[1]) ≫ coherentRightSliceAppendEdgeCone g c =
      coherentRightSliceAppendEdgeCone g ((RZ).map α.op c) := by
  rw [coherentRightSliceAppendEdgeCone, ← Category.assoc,
    appendEdgeConeCoordinates_naturality, Category.assoc,
    coherentRightSliceAppendCone_naturality]
  rfl

/-- 同じ元の追加射の辺全体は、右因子で厳密に固定されている。 -/
lemma coherentRightSliceAppendEdgeCone_fixed {n : ℕ} (c : RZ _⦋n⦌) :
    joinInr (Δ[n] : SSet.{max u v}) Δ[1] ≫ coherentRightSliceAppendEdgeCone g c =
      SSet.yonedaEquiv.symm (coherentNerveEdge g).edge := by
  rw [coherentRightSliceAppendEdgeCone, ← Category.assoc, appendEdgeConeCoordinates_inr,
    Category.assoc, coherentRightSliceAppendCone_tail, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- 実終辺の始点に沿って制限すると、元の同じ全錐を回収する。 -/
lemma coherentRightSliceAppendEdgeCone_start {n : ℕ} (c : RZ _⦋n⦌) :
    joinMap (𝟙 (Δ[n] : SSet.{max u v})) (stdSimplex.δ (1 : Fin 2)) ≫
        coherentRightSliceAppendEdgeCone g c = c.val := by
  rw [coherentRightSliceAppendEdgeCone, ← Category.assoc, appendEdgeConeCoordinates_start,
    coherentRightSliceAppendCone_front]

end SerrePositivity.InfinityCategories.F2
