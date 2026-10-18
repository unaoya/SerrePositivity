module

public import SerrePositivity.KST.Comparison.SliceRightAdjointTrivialFibrations
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# スライスの右随伴による部分切断の対象

概要：A→B と Z→A に対し、B 上の部分切断の対象を実際の引き戻しとして構成する。
方針：基底変換と忘却の右随伴で Z→A を送り、恒等切断に沿って引き戻す。
規約：Segal 1974 Lemma 1.7 の厳密化への補助。制限の同型は別の証明項目。
使われ方：単射に沿う trivial fibration の延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits

/--
概要：恒等切断を表す右随伴への射。
方針：B×_B A→A の第二射影を随伴で転置する。
規約：スライスの終対象は B の恒等射で表す。
使われ方：部分切断の対象を作る引き戻しの片方の射。
-/
def partialSectionUnit {A B : SSet.{u}} (p : A ⟶ B) :
    Over.mk (𝟙 B) ⟶ (sliceFiberFunctor p).rightAdjoint.obj A :=
  (Adjunction.ofIsLeftAdjoint (sliceFiberFunctor p)).homEquiv _ _ (pullback.snd (𝟙 B) p)

/--
概要：B 上の、Z→A の A→B に沿う部分切断の対象。
方針：右随伴で送った Z→A を、恒等切断の転置に沿って引き戻す。
規約：全空間と B への射を持つ実際のスライスの対象。
使われ方：trivial fibration の延長の候補。
-/
def partialSectionObject {Z A B : SSet.{u}} (p : A ⟶ B) (q : Z ⟶ A) : Over B :=
  pullback ((sliceFiberFunctor p).rightAdjoint.map q) (partialSectionUnit p)

/--
概要：元の射が trivial fibration なら、部分切断の対象の B への射も trivial fibration である。
方針：右随伴の全単射的右持ち上げ性の保存と、引き戻しの保存を使う。
規約：この保存自体には A→B の単射性は不要。
使われ方：単射に沿う延長の全体の右持ち上げ性。
-/
theorem partialSectionObject_allMono_rlp {Z A B : SSet.{u}} (p : A ⟶ B) (q : Z ⟶ A)
    (hq : (MorphismProperty.monomorphisms SSet.{u}).rlp q) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (partialSectionObject p q).hom := by
  let G := (sliceFiberFunctor p).rightAdjoint
  let s := partialSectionUnit p
  let t : partialSectionObject p q ⟶ Over.mk (𝟙 B) := pullback.snd (G.map q) s
  have hpb := (IsPullback.of_hasPullback (G.map q) s).map (Over.forget B)
  have ht : (MorphismProperty.monomorphisms SSet.{u}).rlp t.left :=
    (MorphismProperty.monomorphisms SSet.{u}).rlp.of_isPullback hpb
      (sliceFiberRightAdjoint_allMono_rlp p q hq)
  have he : t.left = (partialSectionObject p q).hom := by
    have h := Over.w t
    exact (Category.comp_id t.left).symm.trans h
  rw [← he]
  exact ht

end SerrePositivity.KST.Comparison
