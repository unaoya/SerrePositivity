module
public import SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams

public import SerrePositivity.InfinityCategories.Stable.Exact.CofiberSquareFamily
public import SerrePositivity.InfinityCategories.Stable.LoopDiagramArrows

/-!
概要：普遍 cofiber 四角形の全部分圏と底辺・右辺の評価。
方針：元の四角形の零角と押し出し条件を保持し、安定性で普遍錐の族も得る。
規約：選択済みの全 cofiber 族もこの全部分圏へ入る。使われ方：cofiber 回転の完全性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams

lemma bottom_source (X : SSet.{u}) : bottom X ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      left X ≫ zeroTargetArrowSource X := by
  rw [bottom, zeroTargetArrowSource, ← Category.assoc (left X), left,
    fullSubcomplexLift_ι]
  simp only [Category.assoc, stable_pre_evaluateFunctorAt]
  rfl

lemma right_target (X : SSet.{u}) : right X ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      top X ≫ zeroSourceArrowTarget X := by
  rw [right, zeroSourceArrowTarget, ← Category.assoc (top X), top,
    fullSubcomplexLift_ι]
  simp only [Category.assoc, stable_pre_evaluateFunctorAt]
  rfl

end SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams
