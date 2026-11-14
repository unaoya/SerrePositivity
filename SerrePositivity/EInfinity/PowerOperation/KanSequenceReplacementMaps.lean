module

public import SerrePositivity.EInfinity.PowerOperation.PointedFactorizationFunctor
public import SerrePositivity.KST.Spectra.CofibrantKanSequence
public import SerrePositivity.KST.Spectra.KanSequenceCategory

/-!
# 逐次単射置換の厳密な射への作用

BF 1978 §2 の既存の置換を使う一般の補助。
同じ SOA の関手的な正方形への作用から帰納し、新たな持ち上げの選択を行わない。
［一般∞］移動候補。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory
open SerrePositivity.KST.Spectra

/-- 既存の逐次置換の後続段で分解する、同じ射。 -/
abbrev replacementInput (X : KanSequence.{u}) (n : ℕ) :
    PointedSimplicialSet.circle.{u} ⊗ (KanSequence.replacementStage X n).level.space ⟶
      (X.level (n + 1)).space :=
  PointedSimplicialSet.circle.{u} ◁ (KanSequence.replacementStage X n).projection ≫
    X.sigma n

/-- 前段の射と比較式から、次段の SOA に入れる厳密正方形を得る。 -/
def replacementInputSquare {X Y : KanSequence.{u}} (f : X ⟶ Y) (n : ℕ)
    (s : (KanSequence.replacementStage X n).level.space ⟶
      (KanSequence.replacementStage Y n).level.space)
    (hs : s ≫ (KanSequence.replacementStage Y n).projection =
      (KanSequence.replacementStage X n).projection ≫ f.app n) :
    Arrow.mk (replacementInput X n) ⟶ Arrow.mk (replacementInput Y n) :=
  Arrow.homMk (PointedSimplicialSet.circle.{u} ◁ s) (f.app (n + 1)) (by
    change (PointedSimplicialSet.circle.{u} ◁ s) ≫
      (PointedSimplicialSet.circle.{u} ◁ (KanSequence.replacementStage Y n).projection ≫
        Y.sigma n) =
      (PointedSimplicialSet.circle.{u} ◁ (KanSequence.replacementStage X n).projection ≫
        X.sigma n) ≫ f.app (n + 1)
    rw [← Category.assoc, ← whiskerLeft_comp, hs, whiskerLeft_comp,
      Category.assoc, f.comm n, ← Category.assoc])

/-- 次段の射は、同じ関手的分解の中間対象の射である。 -/
def replacementMapNext {X Y : KanSequence.{u}} (f : X ⟶ Y) (n : ℕ)
    (s : {s : (KanSequence.replacementStage X n).level.space ⟶
      (KanSequence.replacementStage Y n).level.space //
      s ≫ (KanSequence.replacementStage Y n).projection =
        (KanSequence.replacementStage X n).projection ≫ f.app n}) :
    {s : (KanSequence.replacementStage X (n + 1)).level.space ⟶
      (KanSequence.replacementStage Y (n + 1)).level.space //
      s ≫ (KanSequence.replacementStage Y (n + 1)).projection =
        (KanSequence.replacementStage X (n + 1)).projection ≫ f.app (n + 1)} :=
  ⟨pointedFactorizationFunctor.map (replacementInputSquare f n s.val s.property),
    pointedFactorizationFunctor_right _⟩

/-- 各段での射と比較射の可換式を同時に帰納構成する。 -/
def replacementStageMap {X Y : KanSequence.{u}} (f : X ⟶ Y) : (n : ℕ) →
    {s : (KanSequence.replacementStage X n).level.space ⟶
      (KanSequence.replacementStage Y n).level.space //
      s ≫ (KanSequence.replacementStage Y n).projection =
        (KanSequence.replacementStage X n).projection ≫ f.app n}
  | 0 => ⟨f.app 0, by simp [KanSequence.replacementStage]⟩
  | n + 1 => replacementMapNext f n (replacementStageMap f n)

/-- 指定された次段の射は、同じ構造射と厳密に可換。 -/
lemma replacementStageMap_comm {X Y : KanSequence.{u}} (f : X ⟶ Y) (n : ℕ) :
    PointedSimplicialSet.circle.{u} ◁ (replacementStageMap f n).val ≫
      Y.cofibrantReplacement.sigma n =
    X.cofibrantReplacement.sigma n ≫ (replacementStageMap f (n + 1)).val :=
  (pointedFactorizationFunctor_left
    (replacementInputSquare f n (replacementStageMap f n).val
      (replacementStageMap f n).property)).symm

/-- 元の既存置換の間の、厳密な列の射。 -/
def kanSequenceReplacementMap {X Y : KanSequence.{u}} (f : X ⟶ Y) :
    X.cofibrantReplacement ⟶ Y.cofibrantReplacement where
  app n := (replacementStageMap f n).val
  comm n := replacementStageMap_comm f n

/-- 置換射の作用は、元の同じ比較射と可換する。 -/
lemma kanSequenceReplacementMap_projection {X Y : KanSequence.{u}} (f : X ⟶ Y) :
    kanSequenceReplacementMap f ≫ KanSequence.replacementProjection Y =
    KanSequence.replacementProjection X ≫ f := by
  apply KanSequence.Hom.ext_app
  intro n
  exact (replacementStageMap f n).property

end SerrePositivity.EInfinity.PowerOperation
