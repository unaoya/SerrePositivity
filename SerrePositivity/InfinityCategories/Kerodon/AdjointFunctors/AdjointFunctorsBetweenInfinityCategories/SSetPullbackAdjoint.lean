module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.PresheafPullbackAdjoint
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.PullbackAdjointEquivalence
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.Category.ULift

/-!
概要：任意の宇宙の単体集合の通常の引き戻し関手は右随伴を持つ。
方針：単体添字圏を同じ宇宙の小圏へ持ち上げ、前層の slice の一般補題を圏同値で戻す。
規約：単体集合や標的の宇宙を零に固定しない。引き戻す射の充填性は不要。
使われ方：right anodyne 性の引き戻し保存の条件付き定理の仮定を解消する。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：単体集合の通常の引き戻し関手は左随伴である。
方針：AsSmall の添字圏への同値で前層圏の一般定理を適用し、slice の同値で戻す。
規約：任意の Type u の単体集合と任意の射 p に成立する。
使われ方：left fibration に沿う right anodyne な射の引き戻しの一般定理。 -/
lemma cofinalSSetPullback_isLeftAdjoint {E B : SSet.{u}} (p : E ⟶ B) :
    (Over.pullback p).IsLeftAdjoint := by
  let e : SSet.{u} ≌ (AsSmall.{u} SimplexCategory)ᵒᵖ ⥤ Type u :=
    (AsSmall.equiv (C := SimplexCategory)).op.congrLeft
  have : (Over.pullback (e.functor.map p)).IsLeftAdjoint :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.cofinalPresheafPullback_isLeftAdjoint (e.functor.map p)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.cofinalPullback_isLeftAdjoint_of_equivalence e p

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "B.4.4"] _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.cofinalSSetPullback_isLeftAdjoint
