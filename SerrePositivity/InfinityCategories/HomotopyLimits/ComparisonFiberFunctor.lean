module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ComparisonFiberSource
public import SerrePositivity.InfinityCategories.Core.EquivalencePullbackPathLifting

/-!
概要：同じ底上の可換図式が導来 fiber に誘導する実際の射と同値性。
方針：path 成分を保持し、源成分だけを写す射を引き戻しとして同定する。
規約：元の比較射の fibration 性は不要。源の比較が同値なら導来 fiber の比較も同値。
使われ方：Kerodon 4.5.3.24・7.5.4.6、weighted な錐の比較から導来 fiber への移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 概要：同じ底上の源の比較が導来 fiber の間に誘導する実際の射。
方針：path を保持し、源成分へ元の比較を後合成する。
規約：同じ底頂点 b を厳密に固定する。
使われ方：反転した weighted な錐と native な制限の導来 fiber の比較。 -/
def comparisonFiberMap {E D B : SSet.{u}} (p : E ⟶ B) (q : D ⟶ B)
    (f : E ⟶ D) (hf : f ≫ q = p) (b : B _⦋0⦌) :
    comparisonFiber p b ⟶ comparisonFiber q b :=
  comparisonFiberLift q b (comparisonFiberPath p b) (comparisonFiberSource p b ≫ f)
    (by rw [Category.assoc, hf]; exact comparisonFiberPath_source p b)
    (comparisonFiberPath_target p b)

/-- 概要：誘導した導来 fiber の射は path 成分を保つ。
方針：持ち上げの第一成分を計算する。
規約：Kan 性は不要。
使われ方：導来 fiber の引き戻し性と可換式の検証。 -/
lemma comparisonFiberMap_path {E D B : SSet.{u}} (p : E ⟶ B) (q : D ⟶ B)
    (f : E ⟶ D) (hf : f ≫ q = p) (b : B _⦋0⦌) :
    comparisonFiberMap p q f hf b ≫ comparisonFiberPath q b = comparisonFiberPath p b := by
  rw [comparisonFiberMap, comparisonFiberLift_path]

/-- 概要：誘導した導来 fiber の射は源成分の比較と可換。
方針：持ち上げの第二成分を計算する。
規約：元の底上の可換条件と厳密に整合する。
使われ方：導来 fiber の比較を元の源の比較の引き戻しと同定する。 -/
lemma comparisonFiberMap_source {E D B : SSet.{u}} (p : E ⟶ B) (q : D ⟶ B)
    (f : E ⟶ D) (hf : f ≫ q = p) (b : B _⦋0⦌) :
    comparisonFiberMap p q f hf b ≫ comparisonFiberSource q b = comparisonFiberSource p b ≫ f := by
  rw [comparisonFiberMap, comparisonFiberLift_source]

/-- 概要：同じ底上の導来 fiber の比較は元の源の比較の厳密な引き戻し。
方針：標的の path 成分と指定した源成分を元の導来 fiber へ持ち上げる。
規約：Kan 性や fibration 性は要求しない。
使われ方：源の同値による導来 fiber の比較の同値性。 -/
lemma comparisonFiberMap_isPullback {E D B : SSet.{u}} (p : E ⟶ B) (q : D ⟶ B)
    (f : E ⟶ D) (hf : f ≫ q = p) (b : B _⦋0⦌) :
    IsPullback (comparisonFiberMap p q f hf b) (comparisonFiberSource p b)
      (comparisonFiberSource q b) f := by
  let lift (c : PullbackCone (comparisonFiberSource q b) f) : c.pt ⟶ comparisonFiber p b :=
    comparisonFiberLift p b (c.fst ≫ comparisonFiberPath q b) c.snd (by
      rw [Category.assoc, comparisonFiberPath_source, ← Category.assoc, c.condition,
        Category.assoc, hf]) (by
      rw [Category.assoc, comparisonFiberPath_target, SSet.comp_const])
  have hp (c : PullbackCone (comparisonFiberSource q b) f) :
      lift c ≫ comparisonFiberPath p b = c.fst ≫ comparisonFiberPath q b := by
    dsimp only [lift]
    rw [comparisonFiberLift_path]
  have hs (c : PullbackCone (comparisonFiberSource q b) f) :
      lift c ≫ comparisonFiberSource p b = c.snd := by
    dsimp only [lift]
    rw [comparisonFiberLift_source]
  apply IsPullback.of_isLimit (PullbackCone.IsLimit.mk (comparisonFiberMap_source p q f hf b)
    lift ?_ hs ?_)
  · intro c
    apply comparisonFiber_hom_ext q b
    · rw [Category.assoc, comparisonFiberMap_path, hp]
    · rw [Category.assoc, comparisonFiberMap_source, ← Category.assoc, hs]
      exact c.condition.symm
  · intro c m hm₁ hm₂
    apply comparisonFiber_hom_ext p b
    · rw [hp]
      have h := congrArg (· ≫ comparisonFiberPath q b) hm₁
      rw [Category.assoc, comparisonFiberMap_path] at h
      exact h
    · rw [hs]
      exact hm₂

/-- 概要：Kan 複体の同じ底上の源の比較が同値なら、実際の導来 fiber の比較射も同値。
方針：導来 fiber の源射影の fibration 性と同値の引き戻し定理を使う。
規約：元の二つの比較射には fibration 性を要求しない。
使われ方：weighted な錐の比較の同値性を各導来 fiber の実際の射へ移す。 -/
lemma comparisonFiberMap_homotopyEquivalence {E D B : SSet.{u}}
    [KanComplex E] [KanComplex D] [KanComplex B]
    (p : E ⟶ B) (q : D ⟶ B) (f : E ⟶ D) (hf : f ≫ q = p)
    (he : IsSimplicialHomotopyEquivalence f) (b : B _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (comparisonFiberMap p q f hf b) := by
  have : TrivialKanFibration (relativeEquivalencePathMapAt (comparisonFiberSource q b) 1) :=
    relativeEquivalencePathMapAt_trivialKanFibration_of_fibration _ _
  have : Fibration (pullback.fst f (comparisonFiberSource q b)) := by
    apply (SSet.modelCategoryQuillen.fibration_iff _).mpr
    exact (MorphismProperty.rlp _).pullback_fst _ _
      ((SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance)
  have : KanComplex (pullback f (comparisonFiberSource q b)) :=
    isFibrant_of_fibration (pullback.fst f (comparisonFiberSource q b))
  have h := he.isQCatEquivalence.pullback_snd_of_relativePath (comparisonFiberSource q b)
  let pb := (comparisonFiberMap_isPullback p q f hf b).flip
  have h' := (qCatEquivalenceOfIso pb.isoPullback).isQCatEquivalence.comp h
  change IsQCatEquivalence (pb.isoPullback.hom ≫
    pullback.snd f (comparisonFiberSource q b)) at h'
  rw [pb.isoPullback_hom_snd] at h'
  exact h'.isSimplicialHomotopyEquivalence

end
end SerrePositivity.InfinityCategories.HomotopyLimits
