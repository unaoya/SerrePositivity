module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kan.SkeletonFiltrationMono
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
概要：単射と有限骨格間の包含による自然性の正方形は各単体次数で pullback。
方針：標的の小さい骨格への所属を単射の逆像公式で反映する。
規約：部分複体としての骨格と実際の包含をそのまま使う。
使われ方：Goerss–Jardine VIII §1。latching 錐の各固有面の共通部分。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits SSet
namespace SerrePositivity.KST.Spectra.SkeletonFiltration
end SerrePositivity.KST.Spectra.SkeletonFiltration
namespace SerrePositivity.InfinityCategories.Kan.SkeletonFiltration
open SerrePositivity.KST.Spectra.SkeletonFiltration
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 単射に沿う骨格間の包含の正方形は、単体次数ごとに pullback。 -/
lemma transition_app_isPullback {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f]
    {n m : ℕ} (h : n ≤ m) (k : SimplexCategoryᵒᵖ) :
    IsPullback (((transition h).app X).app k) ((map f n).app k)
      ((map f m).app k) (((transition h).app Y).app k) := by
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · ext x
    rfl
  · intro x y hxy
    have he : x.val = y.val := congrArg
      (fun z : ((X.skeleton m : SSet.{u}).obj k) ↦ z.val) hxy.1
    exact Subtype.ext he
  · intro x y hxy
    have he : f.app k x.val = y.val := congrArg
      (fun z : ((Y.skeleton m : SSet.{u}).obj k) ↦ z.val) hxy
    have hx : f.app k x.val ∈ (Y.skeleton n).obj k := by
      rw [he]
      exact y.property
    have hn : x.val ∈ (X.skeleton n).obj k := by
      rw [← preimage_skeleton f n]
      exact hx
    refine ⟨⟨x.val, hn⟩, ?_, ?_⟩
    · exact Subtype.ext rfl
    · exact Subtype.ext he

end SerrePositivity.InfinityCategories.Kan.SkeletonFiltration

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SkeletonFiltration.transition_app_isPullback := _root_.SerrePositivity.InfinityCategories.Kan.SkeletonFiltration.transition_app_isPullback
