module

public import SerrePositivity.KST.NonConnective.SequentialBFArrowStage
public import SerrePositivity.KST.NonConnective.SequentialBFKanArrowFactorization
public import SerrePositivity.KST.Spectra.CofibrantOmegaSequence

/-!
概要：任意の BF 射の、構造射に相対な単射と段ごとの自明 fibration への実分解。
方針：旧再帰式を保持し、一般化された同じ次段構成への特殊化を各段で照合する。
規約：元の射を各段で厳密に回収し、Ω 条件も実際の右射影から証明する。
使われ方：逐次図式の相対 cofibrant 置換と Hom の fibration 塔。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective

variable {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y)

/-- 相対分解の各 Kan 段を、元の同じ BF 射に沿って帰納する。 -/
def sequentialBFArrowStage : (n : ℕ) → SequentialBFArrowStage f n
  | 0 => sequentialBFArrowStageOfKan f 0
      (sequentialBFKanArrowStage (sequentialBFArrowToKanHom f) 0)
  | n + 1 => sequentialBFArrowNext f n (sequentialBFArrowStage n)

/-- 概要：元の旧段は同じ BF 標的への一般化された段の特殊化。
方針：元の再帰式を保持し、一般化された同じ次段構成を帰納して照合する。
規約：旧 eq_1・eq_2 の公開名と型も保持する。
使われ方：旧版の厳密な段データを一般 Kan 列版へ接続する。 -/
lemma sequentialBFArrowStage_toKanStage (n : ℕ) :
    (sequentialBFArrowStage f n).toKanStage =
      sequentialBFKanArrowStage (sequentialBFArrowToKanHom f) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change sequentialBFKanArrowNext (sequentialBFArrowToKanHom f) n
      (sequentialBFArrowStage f n).toKanStage =
      sequentialBFKanArrowNext (sequentialBFArrowToKanHom f) n
        (sequentialBFKanArrowStage (sequentialBFArrowToKanHom f) n)
    rw [ih]

/-- 新しい構造射も保持した、相対分解の中間 Kan 列。 -/
def sequentialBFArrowKanSequence : KanSequence.{u} where
  level n := (sequentialBFArrowStage f n).level
  sigma n := sequentialBFArrowNextSigma f n (sequentialBFArrowStage f n)

/-- 中間 Kan 列から元の標的への、同じ段ごとの右因子。 -/
def sequentialBFArrowKanProjection :
    KanSequence.Hom (sequentialBFArrowKanSequence f) Y.toKanSequence where
  app n := (sequentialBFArrowStage f n).projection
  comm n := sequentialBFArrowNext_projection_comm f n (sequentialBFArrowStage f n)

/-- 右因子の全単射 RLP により、中間 Kan 列も Ω 条件を持つ。 -/
lemma sequentialBFArrowKanSequence_omegaCondition :
    (sequentialBFArrowKanSequence f).OmegaCondition :=
  (sequentialBFArrowKanProjection f).omegaCondition_of_target
    (fun n ↦ (sequentialBFArrowStage f n).projection_rlp) Y.toKanSequence_omega

/-- 相対分解の実中間対象は、同じ宇宙の BF Ω スペクトル。 -/
def sequentialBFArrowMiddle : OmegaSpectrum.{u} :=
  (sequentialBFArrowKanSequence f).toOmegaSpectrum
    (fun n ↦ sequentialBFArrowNextSigma_mono f n (sequentialBFArrowStage f n))
    (sequentialBFArrowKanSequence_omegaCondition f)

/-- 元の源から実中間 BF 対象への厳密な左因子。 -/
def sequentialBFArrowLeft : X ⟶ sequentialBFArrowMiddle f where
  app n := (sequentialBFArrowStage f n).inclusion
  comm n := sequentialBFArrowNext_inclusion_comm f n (sequentialBFArrowStage f n)

/-- 実中間 BF 対象から元の標的への厳密な右因子。 -/
def sequentialBFArrowRight : sequentialBFArrowMiddle f ⟶ Y where
  app := (sequentialBFArrowKanProjection f).app
  comm := (sequentialBFArrowKanProjection f).comm

/-- 構成した二つの元の BF 射の合成は、指定された元の射そのもの。 -/
lemma sequentialBFArrow_fac : sequentialBFArrowLeft f ≫ sequentialBFArrowRight f = f := by
  apply OmegaSpectrum.Hom.ext
  intro n
  exact (sequentialBFArrowStage f n).fac

/-- 右因子は、各段で全ての単射への右持ち上げ性を持つ。 -/
lemma sequentialBFArrowRight_rlp (n : ℕ) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp ((sequentialBFArrowRight f).app n).right :=
  (sequentialBFArrowStage f n).projection_rlp

/-- 相対分解の右因子は、元の BF 射として全整数の π 同型。 -/
lemma sequentialBFArrowRight_piIsomorphism :
    OmegaSpectrum.PiIsomorphism (sequentialBFArrowRight f) :=
  OmegaSpectrum.piIsomorphism_of_levelwise _
    (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _ (sequentialBFArrowRight_rlp f n))

/-- 左因子の零段は実際の単射。 -/
instance sequentialBFArrowLeft_zero_mono : Mono ((sequentialBFArrowLeft f).app 0).right :=
  PointedFactorization.left_mono (f.app 0)

end SerrePositivity.KST.NonConnective
