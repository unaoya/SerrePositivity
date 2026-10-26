module

public import SerrePositivity.KST.NonConnective.SequentialBFKanArrowStage
public import SerrePositivity.KST.Spectra.CofibrantOmegaSequence

/-!
概要：BF 源から Ω 条件を持つ Kan 列への射の、相対 latching 分解。
方針：相対 latching の境界分解をスペクトル段に沿って帰納する。
規約：標的の構造射の単射性を要求せず、Ω 条件は明示証明 hY だけを使う。
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

variable {X : OmegaSpectrum.{u}} {Y : KanSequence.{u}}
  (f : KanSequence.Hom X.toKanSequence Y)

/-- 概要：相対分解の各 Kan 段を、元の同じ BF 射に沿って帰納する。
方針：同じ段別の相対分解と元の厳密構造射を保持する。
規約：標的は Kan 列でよく、BF 中間対象には明示 Ω 条件だけを使う。
使われ方：K-B-S2 の実中間 BF 対象と左右因子。 -/
def sequentialBFKanArrowStage : (n : ℕ) → SequentialBFKanArrowStage f n
  | 0 => {
      level := ⟨PointedFactorization.middle (f.app 0), inferInstance⟩
      inclusion := PointedFactorization.left (f.app 0)
      projection := PointedFactorization.right (f.app 0)
      fac := PointedFactorization.fac (f.app 0)
      projection_rlp := PointedFactorization.right_rlp (f.app 0) }
  | n + 1 => sequentialBFKanArrowNext f n (sequentialBFKanArrowStage n)

/-- 概要：新しい構造射も保持した、相対分解の中間 Kan 列。
方針：同じ段別の相対分解と元の厳密構造射を保持する。
規約：標的は Kan 列でよく、BF 中間対象には明示 Ω 条件だけを使う。
使われ方：K-B-S2 の実中間 BF 対象と左右因子。 -/
def sequentialBFKanArrowKanSequence : KanSequence.{u} where
  level n := (sequentialBFKanArrowStage f n).level
  sigma n := sequentialBFKanArrowNextSigma f n (sequentialBFKanArrowStage f n)

/-- 概要：中間 Kan 列から元の標的への、同じ段ごとの右因子。
方針：同じ段別の相対分解と元の厳密構造射を保持する。
規約：標的は Kan 列でよく、BF 中間対象には明示 Ω 条件だけを使う。
使われ方：K-B-S2 の実中間 BF 対象と左右因子。 -/
def sequentialBFKanArrowKanProjection :
    KanSequence.Hom (sequentialBFKanArrowKanSequence f) Y where
  app n := (sequentialBFKanArrowStage f n).projection
  comm n := sequentialBFKanArrowNext_projection_comm f n (sequentialBFKanArrowStage f n)

/-- 概要：右因子の全単射 RLP により、中間 Kan 列も Ω 条件を持つ。
方針：同じ段別の相対分解と元の厳密構造射を保持する。
規約：標的は Kan 列でよく、BF 中間対象には明示 Ω 条件だけを使う。
使われ方：K-B-S2 の実中間 BF 対象と左右因子。 -/
lemma sequentialBFKanArrowKanSequence_omegaCondition (hY : Y.OmegaCondition) :
    (sequentialBFKanArrowKanSequence f).OmegaCondition :=
  (sequentialBFKanArrowKanProjection f).omegaCondition_of_target
    (fun n ↦ (sequentialBFKanArrowStage f n).projection_rlp) hY

/-- 概要：相対分解の実中間対象は、同じ宇宙の BF Ω スペクトル。
方針：同じ段別の相対分解と元の厳密構造射を保持する。
規約：標的は Kan 列でよく、BF 中間対象には明示 Ω 条件だけを使う。
使われ方：K-B-S2 の実中間 BF 対象と左右因子。 -/
def sequentialBFKanArrowMiddle (hY : Y.OmegaCondition) : OmegaSpectrum.{u} :=
  (sequentialBFKanArrowKanSequence f).toOmegaSpectrum
    (fun n ↦ sequentialBFKanArrowNextSigma_mono f n (sequentialBFKanArrowStage f n))
    (sequentialBFKanArrowKanSequence_omegaCondition f hY)

/-- 概要：元の源から実中間 BF 対象への厳密な左因子。
方針：同じ段別の相対分解と元の厳密構造射を保持する。
規約：標的は Kan 列でよく、BF 中間対象には明示 Ω 条件だけを使う。
使われ方：K-B-S2 の実中間 BF 対象と左右因子。 -/
def sequentialBFKanArrowLeft (hY : Y.OmegaCondition) : X ⟶ sequentialBFKanArrowMiddle f hY where
  app n := (sequentialBFKanArrowStage f n).inclusion
  comm n := sequentialBFKanArrowNext_inclusion_comm f n (sequentialBFKanArrowStage f n)

/-- 概要：実中間 BF 対象から元の標的への厳密な右因子。
方針：同じ段別の相対分解と元の厳密構造射を保持する。
規約：標的は Kan 列でよく、BF 中間対象には明示 Ω 条件だけを使う。
使われ方：K-B-S2 の実中間 BF 対象と左右因子。 -/
def sequentialBFKanArrowRight (hY : Y.OmegaCondition) :
    KanSequence.Hom (sequentialBFKanArrowMiddle f hY).toKanSequence Y where
  app := (sequentialBFKanArrowKanProjection f).app
  comm := (sequentialBFKanArrowKanProjection f).comm

/-- 概要：元の射を各段で厳密に回収する分解式。
方針：同じ段別の相対分解と元の厳密構造射を保持する。
規約：標的は Kan 列でよく、BF 中間対象には明示 Ω 条件だけを使う。
使われ方：K-B-S2 の実中間 BF 対象と左右因子。 -/
lemma sequentialBFKanArrow_fac (hY : Y.OmegaCondition) (n : ℕ) :
    (sequentialBFKanArrowLeft f hY).app n ≫
      (sequentialBFKanArrowRight f hY).app n = f.app n :=
  (sequentialBFKanArrowStage f n).fac

/-- 概要：右因子は、各段で全ての単射への右持ち上げ性を持つ。
方針：同じ段別の相対分解と元の厳密構造射を保持する。
規約：標的は Kan 列でよく、BF 中間対象には明示 Ω 条件だけを使う。
使われ方：K-B-S2 の実中間 BF 対象と左右因子。 -/
lemma sequentialBFKanArrowRight_rlp (hY : Y.OmegaCondition) (n : ℕ) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp ((sequentialBFKanArrowRight f hY).app n).right :=
  (sequentialBFKanArrowStage f n).projection_rlp

/-- 概要：左因子の零段は実際の単射。
方針：同じ段別の相対分解と元の厳密構造射を保持する。
規約：標的は Kan 列でよく、BF 中間対象には明示 Ω 条件だけを使う。
使われ方：K-B-S2 の実中間 BF 対象と左右因子。 -/
instance sequentialBFKanArrowLeft_zero_mono (hY : Y.OmegaCondition) :
    Mono ((sequentialBFKanArrowLeft f hY).app 0).right :=
  PointedFactorization.left_mono (f.app 0)

/-- 概要：左因子の相対 latching 射は、同じ境界分解の左因子そのもの。
方針：同じ段別の相対分解と元の厳密構造射を保持する。
規約：標的は Kan 列でよく、BF 中間対象には明示 Ω 条件だけを使う。
使われ方：K-B-S2 の実中間 BF 対象と左右因子。 -/
lemma sequentialBFKanArrowLeft_latching (hY : Y.OmegaCondition) (n : ℕ) :
    pushout.desc ((sequentialBFKanArrowMiddle f hY).sigma n)
      ((sequentialBFKanArrowLeft f hY).app (n + 1))
      ((sequentialBFKanArrowLeft f hY).comm n) =
      PointedFactorization.left
        (sequentialBFKanArrowNextMap f n (sequentialBFKanArrowStage f n)) := by
  change pushout.desc
    (pushout.inl _ _ ≫ PointedFactorization.left _)
    (pushout.inr _ _ ≫ PointedFactorization.left _) _ = _
  apply pushout.hom_ext
  · exact pushout.inl_desc _ _ _
  · exact pushout.inr_desc _ _ _

/-- 概要：左因子の各相対 latching 射は実際の単射。
方針：同じ段別の相対分解と元の厳密構造射を保持する。
規約：標的は Kan 列でよく、BF 中間対象には明示 Ω 条件だけを使う。
使われ方：K-B-S2 の実中間 BF 対象と左右因子。 -/
lemma sequentialBFKanArrowLeft_latching_mono (hY : Y.OmegaCondition) (n : ℕ) :
    Mono (pushout.desc ((sequentialBFKanArrowMiddle f hY).sigma n)
      ((sequentialBFKanArrowLeft f hY).app (n + 1))
      ((sequentialBFKanArrowLeft f hY).comm n)).right := by
  rw [sequentialBFKanArrowLeft_latching]
  infer_instance

end SerrePositivity.KST.NonConnective
