module

public import SerrePositivity.InfinityCategories.F2.Ind.NestedCosliceCoconeValue
public import SerrePositivity.InfinityCategories.Core.JoinAssociatorRightPair
/-!
概要：指定変換と元の図式の共同余錐から、射影の一致を保つ相対余錐を取り出す。
方針：共同余錐を両部分へ制限し、展開した join 図式を同じ coslice 内へ戻す。
規約：二つの余錐の頂点と値写像を厳密に照合する。
使われ方：Ind の終点評価下の補間余錐への指定変換の追加。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：同じ共同余錐は、指定変換の余錐と元の全図式の余錐を射影の一致付きで与える。
方針：join の括弧と右二因子を回収する。
規約：元の共同余錐を保持。使われ方：終点評価の相対補間。 -/
lemma relativeCocones_of_commonCocone {A B L P X : SSet.{u}} (i : A ⟶ B) (H : B ⟶ X)
    (z : L ⟶ X) (t : A ⟶ sliceUnder z)
    (jB : B ⟶ P) (jT : join L A ⟶ P)
    (hj : i ≫ jB = joinInr L A ≫ jT)
    (F : P ⟶ X) (hB : jB ≫ F = H) (hT : jT ≫ F = sliceUnderUncurry t)
    (c₀ : JoinCocone F) :
    ∃ (c : JoinCocone H) (d : JoinCocone t),
      d.val ≫ sliceUnderProjection z = joinMap i (𝟙 (Δ[0] : SSet.{u})) ≫ c.val := by
  let c : JoinCocone H := ⟨joinMap jB (𝟙 Δ[0]) ≫ c₀.val, by
    rw [← Category.assoc, joinInl_joinMap, Category.assoc, c₀.property, hB]⟩
  let cT : JoinCocone (sliceUnderUncurry t) := ⟨joinMap jT (𝟙 Δ[0]) ≫ c₀.val, by
    rw [← Category.assoc, joinInl_joinMap, Category.assoc, c₀.property, hT]⟩
  let d : JoinCocone t := diagramNestedCosliceDiagramCurry t Δ[0] cT
  refine ⟨c, d, ?_⟩
  change (diagramNestedCosliceDiagramCurry t Δ[0] cT).val ≫ _ = _
  rw [nestedCosliceCocone_value, ← Category.assoc, stableJoinAssociator_rightPair_inv]
  dsimp only [c, cT]
  simp only [← Category.assoc, ← joinMap_comp, Category.comp_id, ← hj]
end SerrePositivity.InfinityCategories.F2.Ind
