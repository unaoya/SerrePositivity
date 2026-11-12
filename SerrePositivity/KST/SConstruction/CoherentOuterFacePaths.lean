module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathFaces

/-! # 外側面は水平区間の全 Path を覆う
概要：最初又は最後に縦辺を加えた単体の水平区間は、元の外側面の全 Path と一致する。
方針：除外頂点が区間の外にあるため、Path 面写像の像が全体になることを使う。
規約：長さ零の水平区間と元の ULift の宇宙を保つ。
使われ方：strict な上下の部分図式の等式から、水平 Hom の全作用を回収する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 終点の縦辺を除いた外側面は、下側の水平区間の全 Path を覆う。 -/
instance coherentLastPathFace_epi (n : ℕ) :
    Epi (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceMap.{u} (Fin.last (n + 1)) 0 (Fin.last n)) := by
  rw [← SSet.Subcomplex.range_eq_top_iff, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.range_pathFaceMap]
  apply Subfunctor.ext
  funext d
  ext P
  change (∀ k, (ULift.up (Fin.last (n + 1)) : ULift.{u} (Fin (n + 2))) ∉
    (P.obj k).I) ↔ True
  simp only [iff_true]
  intro k hk
  have h := (P.obj k).le_right _ hk
  change (Fin.last (n + 1)) ≤ (Fin.last (n + 1)).succAbove (Fin.last n) at h
  simp only [Fin.succAbove_last, Fin.le_def, Fin.val_last, Fin.val_castSucc] at h
  omega

/-- 始点の縦辺を除いた外側面は、上側の水平区間の全 Path を覆う。 -/
instance coherentFirstPathFace_epi (n : ℕ) :
    Epi (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceMap.{u} (0 : Fin (n + 2)) 0 (Fin.last n)) := by
  rw [← SSet.Subcomplex.range_eq_top_iff, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.range_pathFaceMap]
  apply Subfunctor.ext
  funext d
  ext P
  change (∀ k, (ULift.up (0 : Fin (n + 2)) : ULift.{u} (Fin (n + 2))) ∉
    (P.obj k).I) ↔ True
  simp only [iff_true]
  intro k hk
  have h := (P.obj k).left_le _ hk
  change (0 : Fin (n + 2)).succAbove 0 ≤ 0 at h
  simp only [Fin.zero_succAbove, Fin.le_def, Fin.val_succ, Fin.val_zero] at h
  omega

end SerrePositivity.KST.SConstruction
