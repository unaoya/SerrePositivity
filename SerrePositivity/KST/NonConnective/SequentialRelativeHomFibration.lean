module

public import SerrePositivity.KST.NonConnective.SequentialRelativeHomFamily

/-!
概要：相対 latching 単射条件を持つ元の BF 射の前合成は実 Kan fibration。
方針：各段の点つき Hom の充填を、全段で整合した族へまとめる。
規約：モデル圏の instance や射の fibration 性を仮定せず、具体的なホーン RLP を証明する。
使われ方：逐次置換の反変 Hom を fibration の塔として判定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective

/-- 段ごとの二種類の持ち上げ性は、元の全 Raw Hom の前合成へ持ち上がる。 -/
lemma sequentialRawHomPre_hasLiftingProperty {X Z : OmegaSpectrum.{u}} (f : X ⟶ Z)
    (Y : KanSequence.{u}) {A B : SSet.{u}} (j : A ⟶ B)
    (h0 : HasLiftingProperty j (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (f.app 0) (Y.level 0).space))
    (hn : ∀ n, HasLiftingProperty j
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (sequentialRelativeLatchingMap f n) (Y.level (n + 1)).space)) :
    HasLiftingProperty j (RawSpectrumMapping.pre f Y) := by
  constructor
  intro a b sq
  obtain ⟨l, ha, hb, hs⟩ := sequentialRelativeHomFamily f Y j h0 hn a b sq.w
  let m := RawSpectrumMapping.lift Z Y l hs
  refine ⟨⟨{ l := m, fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply RawSpectrumMapping.hom_ext Z Y
    intro n
    rw [Category.assoc, RawSpectrumMapping.lift_evaluation]
    exact ha n
  · apply RawSpectrumMapping.hom_ext X Y
    intro n
    rw [Category.assoc, RawSpectrumMapping.pre_evaluation, ← Category.assoc,
      RawSpectrumMapping.lift_evaluation]
    exact hb n

/-- 相対 cofibrant な元の BF 射の前合成は、実際の全 Raw Hom で Kan fibration。 -/
lemma sequentialRawHomPre_fibration {X Z : OmegaSpectrum.{u}} (f : X ⟶ Z)
    (hf : IsSequentialRelativeCofibration f) (Y : KanSequence.{u}) :
    Fibration (RawSpectrumMapping.pre f Y) := by
  apply (fibration_iff _).2
  intro A B j hj
  apply sequentialRawHomPre_hasLiftingProperty f Y j
  · let : Mono (f.app 0).right := hf.1
    have hp := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_fibration (f.app 0) (Y.level 0).space
    exact (fibration_iff _).1 hp j hj
  · intro n
    let : Mono (sequentialRelativeLatchingMap f n).right := hf.2 n
    have hp := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_fibration
      (sequentialRelativeLatchingMap f n) (Y.level (n + 1)).space
    exact (fibration_iff _).1 hp j hj

end SerrePositivity.KST.NonConnective
