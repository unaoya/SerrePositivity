module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.InputRestrictionProjection

/-!
概要：追加入力を制限して元の基底へ送る全比較を構成する。
方針：二重制限と二重後合成を合成する。
規約：元の図式・全余錐・射影の等式をすべて保持する。
使われ方：指定成分始点を追加した compact 表示の相対交互構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

variable {K L C B : SSet.{u}} (a : K ⟶ C) (i : L ⟶ K) (a₀ : L ⟶ C)
  (hi : i ≫ a = a₀) (z : JoinCocone a) (z₀ : JoinCocone a₀)
  (hzi : joinMap i (𝟙 Δ[0]) ≫ z.val = z₀.val)
  (p : C ⟶ B) (r : L ⟶ B) (hpr : a₀ ≫ p = r) (t : JoinCocone r)
  (hzt : z₀.val ≫ p = t.val)

/-- 概要：追加入力を忘れて元の底へ送る固定標的上の全比較。
方針：元の入力への制限を元の関手の後合成と合成する。
規約：同じ全入力と標的を保つ。
使われ方：異なる入力を持つ二表示の共通の底。 -/
def relativeInputPostcomp :
    sliceOver ((SSet.yonedaEquiv (X := sliceUnder a)).symm z) ⟶
      sliceOver ((SSet.yonedaEquiv (X := sliceUnder r)).symm t) :=
  stableInputRestriction a i a₀ hi z z₀ hzi ≫ stableInputPostcomp a₀ p r hpr z₀ t hzt

/-- 概要：追加入力を持つ比較は元の底への全二重射影を保つ。
方針：制限と後合成の基底射影の可換性を合成する。
規約：全単体集合射の厳密な等式。
使われ方：compact 性と基底余極限性の回収。 -/
lemma relativeInputPostcomp_base_projection :
    relativeInputPostcomp a i a₀ hi z z₀ hzi p r hpr t hzt ≫
      sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder r)).symm t) ≫
        sliceUnderProjection r =
      sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder a)).symm z) ≫
        sliceUnderProjection a ≫ p := by
  dsimp only [relativeInputPostcomp]
  rw [Category.assoc, stableInputPostcomp_base_projection]
  calc
    _ = (stableInputRestriction a i a₀ hi z z₀ hzi ≫
      sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder a₀)).symm z₀) ≫
        sliceUnderProjection a₀) ≫ p := by simp only [Category.assoc]
    _ = _ := by rw [stableInputRestriction_base_projection]; simp only [Category.assoc]

/-- 概要：入力が単射で元の脚が同値を持ち上げれば、追加入力付き比較も同値を持ち上げる。
方針：二つの同値持ち上げを合成する。
規約：追加入力を保つ側の対象を取り直す。
使われ方：共通入力上の比較同型の厳密化。 -/
lemma relativeInputPostcomp_equivalenceLifting [Quasicategory C] [Quasicategory B]
    [Mono i] (hp : F1B.EquivalenceLifting p) :
    F1B.EquivalenceLifting (relativeInputPostcomp a i a₀ hi z z₀ hzi p r hpr t hzt) := by
  have hR : F1B.EquivalenceLifting (stableInputRestriction a i a₀ hi z z₀ hzi) :=
    stableInputRestriction_equivalenceLifting a i a₀ hi z z₀ hzi
  have hP : F1B.EquivalenceLifting (stableInputPostcomp a₀ p r hpr z₀ t hzt) :=
    stableInputPostcomp_equivalenceLifting a₀ p hp r hpr z₀ t hzt
  intro A T j hj he
  have := hR j hj he
  have := hP j hj he
  dsimp only [relativeInputPostcomp]
  infer_instance

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
