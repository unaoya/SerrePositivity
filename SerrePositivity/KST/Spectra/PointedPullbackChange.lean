module

public import SerrePositivity.KST.Spectra.PullbackKanSequence

/-!
概要：引き戻しの左脚を因子分解したときの、実際の引き戻し間の比較。
方針：普遍射を二重引き戻しの正方形として示し、全単射 RLP の基底変換閉性を使う。
規約：点つき射と基礎単体集合の両方で計算する。使われ方：loop の BF 比較の各段。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.KST.Spectra.PointedPullbackChange
variable {E P B X : PointedSimplicialSet.{u}}

/-- 左脚の最初の因子による引き戻し間の実際の射。 -/
def map (q : E ⟶ P) (p : P ⟶ B) (g : X ⟶ B) :
    pullback (q ≫ p) g ⟶ pullback p g :=
  pullback.lift (pullback.fst (q ≫ p) g ≫ q) (pullback.snd (q ≫ p) g)
    (by rw [Category.assoc, pullback.condition])

@[reassoc (attr := simp)]
lemma map_fst (q : E ⟶ P) (p : P ⟶ B) (g : X ⟶ B) :
    map q p g ≫ pullback.fst p g = pullback.fst (q ≫ p) g ≫ q :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma map_snd (q : E ⟶ P) (p : P ⟶ B) (g : X ⟶ B) :
    map q p g ≫ pullback.snd p g = pullback.snd (q ≫ p) g := pullback.lift_snd _ _ _

/-- 比較射は左脚の最初の因子の基底変換である。 -/
lemma isPullback (q : E ⟶ P) (p : P ⟶ B) (g : X ⟶ B) :
    IsPullback (pullback.fst (q ≫ p) g) (map q p g) q (pullback.fst p g) := by
  have h : IsPullback (pullback.fst (q ≫ p) g)
      (map q p g ≫ pullback.snd p g) (q ≫ p) g := by
    rw [map_snd]
    exact IsPullback.of_hasPullback _ _
  exact h.of_bot (map_fst q p g).symm (IsPullback.of_hasPullback p g)

/-- 元の第一因子の全単射 RLP は比較射へ移る。 -/
lemma map_rlp (q : E ⟶ P) (p : P ⟶ B) (g : X ⟶ B)
    (hq : (MorphismProperty.monomorphisms SSet.{u}).rlp q.right) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (map q p g).right :=
  (MorphismProperty.monomorphisms SSet.{u}).rlp.of_isPullback
    ((isPullback q p g).map PointedSimplicialSet.forget) hq

end SerrePositivity.KST.Spectra.PointedPullbackChange
