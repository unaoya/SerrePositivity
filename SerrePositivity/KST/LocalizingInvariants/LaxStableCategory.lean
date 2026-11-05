module

public import SerrePositivity.InfinityCategories.Stable.Verdier.StableCategories
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackStable

/-!
概要：F2 の元の lax pullback と完全射影を K-5 の安定圏の界面へ束ねる。
方針：F2 が供給した安定性と射影の完全性をそのまま使う。
規約：対象・射を置き換えない。使われ方：K-8 の Tamme 分裂定理の入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

variable {C D E : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap D E)

/-- F2 の lax pullback そのものを対象とする小さい安定 ∞ 圏。 -/
def laxCategory : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u} where
  obj := F2.laxPullback p.hom q.hom
  isQuasicategory := inferInstance
  isStable := inferInstance

/-- 元の第一射影。完全性の証明は F2 から読み取り専用で使う。 -/
def laxFst : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (laxCategory p q) C where
  hom := F2.laxPullbackFst p.hom q.hom
  isExact := F2.laxPullbackFst_isExactFunctor p.hom q.hom

/-- 元の第二射影。 -/
def laxSnd : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (laxCategory p q) D where
  hom := F2.laxPullbackSnd p.hom q.hom
  isExact := F2.laxPullbackSnd_isExactFunctor p.hom q.hom

end SerrePositivity.KST.LocalizingInvariants
