module

public import SerrePositivity.KST.Spectra.RawSpectrumRelativeCornerFamily
public import SerrePositivity.KST.Spectra.RawSpectrumMappingPreNaturality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence

/-!
概要：元の全 Raw Hom の二変数 corner 写像とその全単射 RLP。
方針：実前合成・後合成の引き戻しを作り、全段の相対充填を元の整合 Hom へ束ねる。
規約：両射影を元の射のまま保持し、モデル圏の instance を入力しない。
使われ方：相対 BF 右射影と指定左因子を全 Hom 上で同時に自然にする。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.KST.NonConnective
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 概要：元の源上の族と元の射影先の族を保持する実 corner 標的。
方針：全 Raw Hom の後合成と前合成の実引き戻しを取る。
規約：第一射影は源上の族、第二射影は射影先の族。
使われ方：全 Hom の二つの境界を同時に指定する。 -/
abbrev relativeCornerTarget {X R : OmegaSpectrum.{u}} (i : X ⟶ R)
    {E Z : KanSequence.{u}} (q : KanSequence.Hom E Z) : SSet.{u} :=
  pullback (post X q) (pre i Z)

/-- 概要：元の全 Raw Hom の射を二つの元の制限へ写す実 corner 写像。
方針：前合成と後合成の厳密交換則で実引き戻しへ持ち上げる。
規約：別の Hom 模型への置換を行わない。
使われ方：相対 BF の全 Hom 比較の元の射。 -/
def relativeCorner {X R : OmegaSpectrum.{u}} (i : X ⟶ R)
    {E Z : KanSequence.{u}} (q : KanSequence.Hom E Z) :
    space R E ⟶ relativeCornerTarget i q :=
  pullback.lift (pre i E) (post R q) (by
    have h := congrArg Under.Hom.right (pointedPre_post i q)
    simp only [Under.comp_right] at h
    exact h.symm)

/-- 概要：corner の第一射影は元の全 Hom の前合成そのもの。
方針：実引き戻しへの持ち上げの第一射影式を使う。
規約：全単体上の厳密等式。
使われ方：元の源上の族の回収。 -/
@[reassoc (attr := simp)]
lemma relativeCorner_fst {X R : OmegaSpectrum.{u}} (i : X ⟶ R)
    {E Z : KanSequence.{u}} (q : KanSequence.Hom E Z) :
    relativeCorner i q ≫ pullback.fst _ _ = pre i E :=
  pullback.lift_fst _ _ _

/-- 概要：corner の第二射影は元の全 Hom の後合成そのもの。
方針：実引き戻しへの持ち上げの第二射影式を使う。
規約：全単体上の厳密等式。
使われ方：元の射影先の族の回収。 -/
@[reassoc (attr := simp)]
lemma relativeCorner_snd {X R : OmegaSpectrum.{u}} (i : X ⟶ R)
    {E Z : KanSequence.{u}} (q : KanSequence.Hom E Z) :
    relativeCorner i q ≫ pullback.snd _ _ = post R q :=
  pullback.lift_snd _ _ _

/-- 概要：corner の源側の射影の全段評価は元の段射への前合成。
方針：第一射影と元の全 Hom の評価式を合成する。
規約：自然数の全段と全 Hom パラメータを保持する。
使われ方：指定左因子の厳密境界照合。 -/
@[reassoc] lemma relativeCorner_fst_evaluation {X R : OmegaSpectrum.{u}} (i : X ⟶ R)
    {E Z : KanSequence.{u}} (q : KanSequence.Hom E Z) (n : ℕ) :
    relativeCorner i q ≫ pullback.fst _ _ ≫ evaluation X E n =
      evaluation R E n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (i.app n) (E.level n).space := by
  rw [← Category.assoc, relativeCorner_fst, pre_evaluation]

/-- 概要：corner の標的側の射影の全段評価は元の段射への後合成。
方針：第二射影と元の全 Hom の評価式を合成する。
規約：射影の各段の元の射を保持する。
使われ方：指定右射影の厳密境界照合。 -/
@[reassoc] lemma relativeCorner_snd_evaluation {X R : OmegaSpectrum.{u}} (i : X ⟶ R)
    {E Z : KanSequence.{u}} (q : KanSequence.Hom E Z) (n : ℕ) :
    relativeCorner i q ≫ pullback.snd _ _ ≫ evaluation R Z n =
      evaluation R E n ≫ (PointedObject.basedHomMap (R.level n).space (q.app n)).right := by
  rw [← Category.assoc, relativeCorner_snd, post_evaluation]

/-- 概要：相対 cofibration と全段の全単射 RLP から、元の二変数 corner の全単射 RLP。
方針：三つの境界を固定した全段の実充填を元の全 Raw Hom へ束ねる。
規約：corner の RLP を明示入力として残さない。
使われ方：相対 BF 置換の全 Hom 自然性の構成。 -/
lemma relativeCorner_rlp_monomorphisms {X R : OmegaSpectrum.{u}} (i : X ⟶ R)
    (hi : IsSequentialRelativeCofibration i) {E Z : KanSequence.{u}}
    (q : KanSequence.Hom E Z)
    (hq : ∀ n, (MorphismProperty.monomorphisms SSet.{u}).rlp (q.app n).right) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (relativeCorner i q) := by
  intro T U j hj
  let : Mono j := hj
  constructor
  intro a b sq
  have ha : a ≫ post R q = j ≫ (b ≫ pullback.snd _ _) := by
    have h := congrArg (· ≫ pullback.snd _ _) sq.w
    simpa only [Category.assoc, relativeCorner_snd] using h
  have hc : a ≫ pre i E = j ≫ (b ≫ pullback.fst _ _) := by
    have h := congrArg (· ≫ pullback.fst _ _) sq.w
    simpa only [Category.assoc, relativeCorner_fst] using h
  have hbc : (b ≫ pullback.snd _ _) ≫ pre i Z =
      (b ≫ pullback.fst _ _) ≫ post X q := by
    rw [Category.assoc, Category.assoc, ← pullback.condition]
  obtain ⟨f, hf, hqf, hif, hs⟩ := relativeCornerFamily i hi q hq j a
    (b ≫ pullback.snd _ _) (b ≫ pullback.fst _ _) hbc ha hc
  let l := lift R E f hs
  refine ⟨⟨{ l := l, fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply hom_ext R E
    intro n
    rw [Category.assoc, lift_evaluation]
    exact hf n
  · apply pullback.hom_ext
    · rw [Category.assoc, relativeCorner_fst]
      apply hom_ext X E
      intro n
      rw [Category.assoc, pre_evaluation, ← Category.assoc, lift_evaluation]
      exact hif n
    · rw [Category.assoc, relativeCorner_snd]
      apply hom_ext R Z
      intro n
      rw [Category.assoc, post_evaluation, ← Category.assoc, lift_evaluation]
      exact hqf n

/-- 概要：同じ元の二変数 corner は実際の自明 Kan fibration。
方針：構成済みの全単射 RLP を束ねる。
規約：corner の射と二つの境界を変更しない。
使われ方：指定単位・右射影の全族を同時に回収する比較。 -/
lemma relativeCorner_trivialKanFibration {X R : OmegaSpectrum.{u}} (i : X ⟶ R)
    (hi : IsSequentialRelativeCofibration i) {E Z : KanSequence.{u}}
    (q : KanSequence.Hom E Z)
    (hq : ∀ n, (MorphismProperty.monomorphisms SSet.{u}).rlp (q.app n).right) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (relativeCorner i q) :=
  ⟨relativeCorner_rlp_monomorphisms i hi q hq⟩

end SerrePositivity.KST.Spectra.RawSpectrumMapping
