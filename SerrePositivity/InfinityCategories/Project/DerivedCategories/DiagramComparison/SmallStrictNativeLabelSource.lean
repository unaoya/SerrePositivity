module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NativeLabelCoordinates
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarDiagram

/-!
概要：元の strict 射列の native 混合成分のラベルが、元の同じ先頭対象を持つことを示す。
方針：元の部分集合の順序列挙の第零項と、最後を除いた最小点を照合する。
規約：係数加群の対象の一致から添字の一致を推論しない。元の添字圏で証明する。
使われ方：3b-3 R6、同じ自然変換の先頭成分を native 列の自然性へ渡す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable {J : Type} [SmallCategory J]

/-- 同じ部分集合ラベルの第零の対象は、元の射列の同じ最小点の対象。 -/
lemma smallStrictSubsetLabel_obj_zero {n r : ℕ}
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌)
    (T : Finset (Fin (n + 1))) (hc : T.card = r + 1) (hT : T.Nonempty) :
    (dgCoherentBarSubsetLabel s T r hc).2.down.obj 0 = s.down.obj (T.min' hT) := by
  change s.down.obj ((T.orderEmbOfFin hc) 0) = _
  exact congrArg s.down.obj (Finset.orderEmbOfFin_zero hc (Nat.succ_pos r))

/-- 同じ native 混合成分のラベルの先頭は、元の同じ旧頂点の対象である。 -/
lemma smallStrictBianchiLabel_obj_zero {n : ℕ}
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌)
    (T : Finset (Fin (n + 2))) (a : Fin (n + 1)) (hT : 2 ≤ T.card)
    (ha : a.castSucc = T.min' (Index.nonempty hT))
    (hb : Fin.last (n + 1) = T.max' (Index.nonempty hT)) :
    (dgCoherentBarBianchiLabel s T hT hb).2.down.obj 0 = s.down.obj a := by
  have hl : Fin.last (n + 1) ∈ T := hb ▸ T.max'_mem _
  have hK := withoutLast_nonempty hT hl
  have hm : ((withoutLast T).min' hK).castSucc = a.castSucc :=
    (min_withoutLast T hT hl).trans ha.symm
  have he : (withoutLast T).min' hK = a := Fin.ext (congrArg (fun z : Fin (n + 2) => z.val) hm)
  unfold dgCoherentBarBianchiLabel
  rw [smallStrictSubsetLabel_obj_zero _ _ _ hK, he]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
