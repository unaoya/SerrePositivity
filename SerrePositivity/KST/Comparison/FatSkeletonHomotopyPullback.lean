module

public import SerrePositivity.KST.Comparison.FatSkeletonSuccessor
public import SerrePositivity.KST.Comparison.FatSkeletonZero
public import SerrePositivity.KST.Comparison.HomotopyPullbackGeneralPasting

/-!
# fat realization の全ての有限骨格の行の比較

概要：面のホモトピー引き戻し性から、全ての行の有限骨格への比較を証明する。
方針：零骨格の同型から始め、境界の有限被覆と付着の pushout で帰納する。
規約：Segal 1974 Proposition 1.6 の有限骨格の段階。各行の射は Kan fibration とする。
使われ方：順序列の telescope を介した fat realization 全体への比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial

/--
概要：各面の比較から全ての低い行の有限骨格への比較が従う。
方針：境界の比較と単射な脚の pushout による帰納、一般の横の貼り合わせを使う。
規約：有限骨格の比較のみを結論とし、無限骨格や対角への比較は別途扱う。
使われ方：Segal Proposition 1.6 の無限骨格の極限段階。
-/
theorem fatSkeletonRow_homotopyPullback
    {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (α : F ⟶ G)
    (hKan : ∀ m, SSet.modelCategoryQuillen.J.rlp (α.app (op ⦋m⦌)))
    (hface : ∀ (m k : ℕ) (θ : ⦋m⦌ ⟶ ⦋k⦌), Function.Injective θ →
      IsHomotopyPullback (CommSq.mk (α.naturality θ.op))) :
    ∀ (n m : ℕ) (hm : m ≤ n), IsHomotopyPullback
      (CommSq.mk (fatSkeletonRowOfLE_map α hm)) := by
  intro n
  induction n with
  | zero =>
    intro m hm
    have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
    subst m
    let : IsIso (fatSkeletonRowOfLE F hm) := by
      simpa only [fatSkeletonRowOfLE, SSet.Subcomplex.homOfLE_refl, Category.comp_id]
        using (inferInstance : IsIso (fatSkeletonRow F 0))
    let : IsIso (fatSkeletonRowOfLE G hm) := by
      simpa only [fatSkeletonRowOfLE, SSet.Subcomplex.homOfLE_refl, Category.comp_id]
        using (inferInstance : IsIso (fatSkeletonRow G 0))
    exact isHomotopyPullback_of_fibration
      (IsPullback.of_horiz_isIso (CommSq.mk (fatSkeletonRowOfLE_map α hm)))
      (SSet.modelCategoryQuillen.J.rlp.of_isIso _)
  | succ n ih =>
    have hboundary := fatBoundaryAttachment_homotopyPullback α n hKan hface ih
    obtain ⟨hstep, hnew⟩ := fatSkeleton_successor_homotopyPullback α n (hKan (n + 1)) hboundary
    intro m hm
    by_cases heq : m = n + 1
    · subst m
      exact hnew
    · have hm' : m ≤ n := by omega
      exact isHomotopyPullback_paste_horiz (CommSq.mk (fatSkeletonRowOfLE_map α hm'))
        (CommSq.mk (fatSkeletonStep_map α n)) (ih m hm') hstep

end SerrePositivity.KST.Comparison
