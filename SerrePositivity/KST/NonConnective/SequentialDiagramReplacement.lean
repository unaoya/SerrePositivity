module

public import SerrePositivity.KST.NonConnective.SequentialRelativeCofibration
public import SerrePositivity.KST.NonConnective.SequentialIndexFunctors

/-!
概要：元の任意の逐次 BF 図式の、相対 cofibrant な図式への実際の置換。
方針：前の段の比較と元の次の射の合成を、相対 BF 分解で帰納的に分解する。
規約：元の図式への厳密な自然変換と、その全整数 π 同型性を保持する。
使われ方：全反変 Hom の fibration 塔による ∞ 余極限性の判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective

/-- 置換した各 BF 対象と、元の同じ入力段への実際の比較射。 -/
def sequentialDiagramReplacementStage (D : SpectrumSequence.{u}) :
    (n : ℕ) → Σ X : OmegaSpectrum.{u}, X ⟶ D.obj ⟨n⟩
  | 0 => ⟨D.obj ⟨0⟩, 𝟙 _⟩
  | n + 1 =>
    let f := (sequentialDiagramReplacementStage D n).2 ≫ D.map (homOfLE (Nat.le_succ n))
    ⟨sequentialBFArrowMiddle f, sequentialBFArrowRight f⟩

/-- 置換列の隣接射は、同じ相対分解の左因子。 -/
def sequentialDiagramReplacementStep (D : SpectrumSequence.{u}) (n : ℕ) :
    (sequentialDiagramReplacementStage D n).1 ⟶
      (sequentialDiagramReplacementStage D (n + 1)).1 :=
  sequentialBFArrowLeft
    ((sequentialDiagramReplacementStage D n).2 ≫ D.map (homOfLE (Nat.le_succ n)))

/-- 元の入力との比較は、全ての隣接射で厳密に可換。 -/
lemma sequentialDiagramReplacementStep_comparison (D : SpectrumSequence.{u}) (n : ℕ) :
    sequentialDiagramReplacementStep D n ≫ (sequentialDiagramReplacementStage D (n + 1)).2 =
      (sequentialDiagramReplacementStage D n).2 ≫ D.map (homOfLE (Nat.le_succ n)) :=
  sequentialBFArrow_fac _

/-- 置換した射列を、元の逐次添字上の実 BF 関手として保持する。 -/
def sequentialDiagramReplacement (D : SpectrumSequence.{u}) : SpectrumSequence.{u} :=
  sequentialIndexDown ⋙ Functor.ofSequence (sequentialDiagramReplacementStep D)

/-- 置換した元の逐次図式から、元の入力図式への厳密な自然変換。 -/
def sequentialDiagramReplacementComparison (D : SpectrumSequence.{u}) :
    sequentialDiagramReplacement D ⟶ D where
  app a := (sequentialDiagramReplacementStage D a.down).2
  naturality a b f := by
    let η : Functor.ofSequence (sequentialDiagramReplacementStep D) ⟶ sequentialIndexUp ⋙ D :=
      NatTrans.ofSequence (fun n ↦ (sequentialDiagramReplacementStage D n).2) (by
        intro n
        rw [Functor.ofSequence_map_homOfLE_succ]
        exact sequentialDiagramReplacementStep_comparison D n)
    have h := η.naturality (sequentialIndexDown.map f)
    change (Functor.ofSequence (sequentialDiagramReplacementStep D)).map
      (sequentialIndexDown.map f) ≫ (sequentialDiagramReplacementStage D b.down).2 =
        (sequentialDiagramReplacementStage D a.down).2 ≫
          D.map (sequentialIndexUp.map (sequentialIndexDown.map f)) at h
    rw [sequentialIndexUpDown_map] at h
    exact h

/-- 置換列の各隣接射は、相対 latching 単射条件を実際に満たす。 -/
lemma sequentialDiagramReplacementStep_isRelativeCofibration
    (D : SpectrumSequence.{u}) (n : ℕ) :
    IsSequentialRelativeCofibration (sequentialDiagramReplacementStep D n) :=
  sequentialBFArrowLeft_isRelativeCofibration _

/-- 同じ比較自然変換は、全ての元の入力段で全整数 π 同型。 -/
lemma sequentialDiagramReplacementComparison_piIsomorphism
    (D : SpectrumSequence.{u}) (a : SequentialIndex.{u}) :
    OmegaSpectrum.PiIsomorphism ((sequentialDiagramReplacementComparison D).app a) := by
  rcases a with ⟨n⟩
  cases n with
  | zero => exact OmegaSpectrum.PiIsomorphism.id _
  | succ n => exact sequentialBFArrowRight_piIsomorphism _

end SerrePositivity.KST.NonConnective
