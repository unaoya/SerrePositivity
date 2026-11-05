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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams

lemma bottom_source (X : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.bottom X ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.left X ≫ zeroTargetArrowSource X := by
  rw [_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.bottom, zeroTargetArrowSource, ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.left X), _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.left,
    fullSubcomplexLift_ι]
  simp only [Category.assoc, stable_pre_evaluateFunctorAt]
  rfl

lemma right_target (X : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.right X ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.top X ≫ zeroSourceArrowTarget X := by
  rw [_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.right, zeroSourceArrowTarget, ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.top X), _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.top,
    fullSubcomplexLift_ι]
  simp only [Category.assoc, stable_pre_evaluateFunctorAt]
  rfl

end SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams
