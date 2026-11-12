module

public import SerrePositivity.KST.LocalizingInvariants.InitialConeTensorShape
public import SerrePositivity.KST.LocalizingInvariants.PushoutComparisonHomotopy
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
概要：左錐の積の元の境界を、元の有限図式側と尾部側の実 pushout として貼る。
方針：既存の右錐境界の pushout を単体的反転で写す。
規約：反転した全台を使い、元の境界包含と実図式の両制限を厳密に保つ。
使われ方：c5 の全境界 p と全比較 e を、二つの回収済み図式から組み立てる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

def initialConeTensorOldInclusion (A L : SSet.{u}) :
    (A.op ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join L.op (Δ[0] : SSet.{u})).op ⟶ initialConeTensorCorner A L :=
  SSet.opFunctor.map (pushout.inl (A.op ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl L.op (Δ[0] : SSet.{u}))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A.op Δ[0] ▷ L.op))

def initialConeTensorTailInclusion (A L : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A.op (Δ[0] : SSet.{u}) ⊗ L.op).op ⟶ initialConeTensorCorner A L :=
  SSet.opFunctor.map (pushout.inr (A.op ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl L.op (Δ[0] : SSet.{u}))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A.op Δ[0] ▷ L.op))

instance initialConeTensorOldInclusion_mono (A L : SSet.{u}) :
    Mono (initialConeTensorOldInclusion A L) := by
  have : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A.op (Δ[0] : SSet.{u}) ▷ L.op) := (tensorRight _).map_mono _
  have hm : Mono (pushout.inl (A.op ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl L.op (Δ[0] : SSet.{u}))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A.op Δ[0] ▷ L.op)) :=
    Adhesive.mono_of_isPushout_of_mono_right (IsPushout.of_hasPushout _ _)
  unfold initialConeTensorOldInclusion
  rw [NatTrans.mono_iff_mono_app] at hm ⊢
  intro n
  exact hm _

instance initialConeTensorTailInclusion_mono (A L : SSet.{u}) :
    Mono (initialConeTensorTailInclusion A L) := by
  have : Mono (A.op ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl L.op (Δ[0] : SSet.{u})) := (tensorLeft _).map_mono _
  have hm : Mono (pushout.inr (A.op ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl L.op (Δ[0] : SSet.{u}))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A.op Δ[0] ▷ L.op)) :=
    Adhesive.mono_of_isPushout_of_mono_left (IsPushout.of_hasPushout _ _)
  unfold initialConeTensorTailInclusion
  rw [NatTrans.mono_iff_mono_app] at hm ⊢
  intro n
  exact hm _

/-- 元の二つの実境界は、同じ共有部分に沿う pushout で全境界を与える。 -/
lemma initialConeTensorCorner_isPushout (A L : SSet.{u}) :
    IsPushout (SSet.opFunctor.map (A.op ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl L.op (Δ[0] : SSet.{u})))
      (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A.op (Δ[0] : SSet.{u}) ▷ L.op))
      (initialConeTensorOldInclusion A L) (initialConeTensorTailInclusion A L) := by
  have : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
  exact (IsPushout.of_hasPushout (A.op ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl L.op (Δ[0] : SSet.{u}))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A.op Δ[0] ▷ L.op)).map SSet.opFunctor

variable {A L X : SSet.{u}}
  (F : (A.op ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join L.op (Δ[0] : SSet.{u})).op ⟶ X)
  (G : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A.op (Δ[0] : SSet.{u}) ⊗ L.op).op ⟶ X)
  (w : SSet.opFunctor.map (A.op ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl L.op (Δ[0] : SSet.{u})) ≫ F =
    SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A.op (Δ[0] : SSet.{u}) ▷ L.op) ≫ G)

/-- 回収済みの元の図式と尾部から、同じ全実境界を構成する。 -/
def initialConeTensorCornerGlue : initialConeTensorCorner A L ⟶ X :=
  (initialConeTensorCorner_isPushout A L).desc F G w

lemma initialConeTensorCornerGlue_old :
    initialConeTensorOldInclusion A L ≫ initialConeTensorCornerGlue F G w = F :=
  (initialConeTensorCorner_isPushout A L).inl_desc _ _ _

lemma initialConeTensorCornerGlue_tail :
    initialConeTensorTailInclusion A L ≫ initialConeTensorCornerGlue F G w = G :=
  (initialConeTensorCorner_isPushout A L).inr_desc _ _ _

end SerrePositivity.KST.LocalizingInvariants
