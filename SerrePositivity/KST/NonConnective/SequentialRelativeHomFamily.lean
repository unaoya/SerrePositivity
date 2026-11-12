module

public import SerrePositivity.KST.NonConnective.SequentialRelativeHomNext

/-!
概要：相対 BF 射による前合成の持ち上げを、全スペクトル段で構成する。
方針：零段の持ち上げから相対 latching の持ち上げを帰納し、三つの境界条件を保持する。
規約：必要な段ごとの持ち上げ性を明示し、元の部分族と元の源を変更しない。
使われ方：反変 Raw Hom の Kan fibration 性の実証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective

/-- 指定パラメータと元の BF 源を固定した、全スペクトル段の整合した持ち上げ族。 -/
lemma sequentialRelativeHomFamily {X Z : OmegaSpectrum.{u}} (f : X ⟶ Z)
    (Y : KanSequence.{u}) {A B : SSet.{u}} (j : A ⟶ B)
    (h0 : HasLiftingProperty j (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (f.app 0) (Y.level 0).space))
    (hn : ∀ n, HasLiftingProperty j
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (sequentialRelativeLatchingMap f n) (Y.level (n + 1)).space))
    (a : A ⟶ RawSpectrumMapping.space Z Y) (b : B ⟶ RawSpectrumMapping.space X Y)
    (h : a ≫ RawSpectrumMapping.pre f Y = j ≫ b) :
    ∃ l : ∀ n, B ⟶ (PointedObject.basedHom (Z.level n).space (Y.level n).space).right,
      (∀ n, j ≫ l n = a ≫ RawSpectrumMapping.evaluation Z Y n) ∧
      (∀ n, l n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (f.app n) (Y.level n).space =
        b ≫ RawSpectrumMapping.evaluation X Y n) ∧
      (∀ n, l (n + 1) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (Z.sigma n) (Y.level (n + 1)).space =
        l n ≫ RawSpectrumMapping.step Z Y n) := by
  let LiftAt (n : ℕ) := {l : B ⟶
      (PointedObject.basedHom (Z.level n).space (Y.level n).space).right //
      j ≫ l = a ≫ RawSpectrumMapping.evaluation Z Y n ∧
        l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (f.app n) (Y.level n).space =
          b ≫ RawSpectrumMapping.evaluation X Y n}
  have hb (n : ℕ) : (a ≫ RawSpectrumMapping.evaluation Z Y n) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (f.app n) (Y.level n).space =
        j ≫ (b ≫ RawSpectrumMapping.evaluation X Y n) := by
    rw [Category.assoc, ← RawSpectrumMapping.pre_evaluation,
      ← Category.assoc, h, Category.assoc]
  have hzero : Nonempty (LiftAt 0) := by
    let : HasLiftingProperty j (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (f.app 0) (Y.level 0).space) := h0
    let sq : CommSq (a ≫ RawSpectrumMapping.evaluation Z Y 0) j
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (f.app 0) (Y.level 0).space)
      (b ≫ RawSpectrumMapping.evaluation X Y 0) := ⟨hb 0⟩
    exact ⟨⟨sq.lift, sq.fac_left, sq.fac_right⟩⟩
  have hnext (n : ℕ) (prev : LiftAt n) : ∃ next : LiftAt (n + 1),
      next.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (Z.sigma n) (Y.level (n + 1)).space =
        prev.val ≫ RawSpectrumMapping.step Z Y n := by
    let : HasLiftingProperty j
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (sequentialRelativeLatchingMap f n) (Y.level (n + 1)).space) := hn n
    have huv : (prev.val ≫ RawSpectrumMapping.step Z Y n) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (PointedSimplicialSet.circle.{u} ◁ f.app n) (Y.level (n + 1)).space =
      (b ≫ RawSpectrumMapping.evaluation X Y (n + 1)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space := by
      rw [Category.assoc, sequentialRawStep_pre, ← Category.assoc, prev.property.2,
        Category.assoc, ← RawSpectrumMapping.evaluation_condition, ← Category.assoc]
    have hu : j ≫ (prev.val ≫ RawSpectrumMapping.step Z Y n) =
        (a ≫ RawSpectrumMapping.evaluation Z Y (n + 1)) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (Z.sigma n) (Y.level (n + 1)).space := by
      rw [← Category.assoc, prev.property.1, Category.assoc,
        ← RawSpectrumMapping.evaluation_condition, ← Category.assoc]
    obtain ⟨l, hl, hs, hf⟩ := sequentialRelativeHomNext f n (Y.level (n + 1)).space j
      (a ≫ RawSpectrumMapping.evaluation Z Y (n + 1))
      (prev.val ≫ RawSpectrumMapping.step Z Y n)
      (b ≫ RawSpectrumMapping.evaluation X Y (n + 1)) huv hu (hb (n + 1)).symm
    exact ⟨⟨l, hl, hf⟩, hs⟩
  let stage : ∀ n, LiftAt n := Nat.rec (Classical.choice hzero)
    (fun n prev ↦ (hnext n prev).choose)
  exact ⟨fun n ↦ (stage n).val, fun n ↦ (stage n).property.1,
    fun n ↦ (stage n).property.2, fun n ↦ (hnext n (stage n)).choose_spec⟩

end SerrePositivity.KST.NonConnective
