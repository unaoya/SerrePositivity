module

public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentRightSliceAppendEdgeCone
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.AppendEdgeConeMiddle
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DoubleRightPointMiddle
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentAppendPenultimateFace
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentRightSlicePostSimplex

/-!
概要：追加した実錐の中間終点を除く全面は、元の指定射で後合成した全錐そのもの。
方針：元の追加単体の最終手前の面を、二重 join の座標へ戻す。
規約：元の全錐・指定後合成を保持。使われ方：実四面体の 013 面の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {Z W : C} (g : Z ⟶ W)
local notation "RZ" => sliceOver (SSet.yonedaEquiv.symm (coherentNerveVertex Z))

/-- 元の追加錐の中間終点を除くと、同じ指定射の元の全錐後合成。 -/
lemma coherentRightSliceAppendCone_middle {n : ℕ} (c : RZ _⦋n⦌) :
    joinMap (joinInl (Δ[n] : SSet.{max u v}) Δ[0]) (𝟙 Δ[0]) ≫
        coherentRightSliceAppendCone g c = (coherentRightSlicePostSimplex g c).val := by
  rw [coherentRightSliceAppendCone, ← Category.assoc, doubleRightPointCoordinates_middle,
    Category.assoc, SSet.yonedaEquiv_symm_naturality_left]
  change (joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm
    ((SimplicialNerve C).δ (Fin.last (n + 1)).castSucc
      (coherentSimplexAppendMorphism _ _)) = _
  rw [coherentSimplexAppendMorphism_face_penultimate]
  rfl

/-- 元の実終辺の終点に沿う全面は、同じ元の全錐後合成。 -/
lemma coherentRightSliceAppendEdgeCone_end {n : ℕ} (c : RZ _⦋n⦌) :
    joinMap (𝟙 (Δ[n] : SSet.{max u v})) (stdSimplex.δ (0 : Fin 2)) ≫
        coherentRightSliceAppendEdgeCone g c = (coherentRightSlicePostSimplex g c).val := by
  rw [coherentRightSliceAppendEdgeCone, ← Category.assoc, appendEdgeConeCoordinates_end,
    coherentRightSliceAppendCone_middle]

end SerrePositivity.InfinityCategories.F2
