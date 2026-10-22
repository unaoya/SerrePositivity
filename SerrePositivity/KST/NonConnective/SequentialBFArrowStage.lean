module

public import SerrePositivity.KST.NonConnective.SequentialPointedPushoutMono
public import SerrePositivity.KST.Spectra.PointedFactorization

/-!
概要：BF 射を構造射に沿って相対分解する一段の実データ。
方針：既存の源と新しい前段の suspension を押し出し、元の標的への射を境界分解する。
規約：右因子の全単射 RLP を実証し、Ω 条件を入力にしない。
使われ方：逐次図式を相対 cofibrant な図式へ置換する帰納構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective

/-- 指定された元の BF 射の一段の相対分解。 -/
structure SequentialBFArrowStage {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (n : ℕ) where
  /-- 新しい点つき Kan 段。 -/
  level : PointedKanComplex.{u}
  /-- 元の源の同じ段からの左因子。 -/
  inclusion : (X.level n).space ⟶ level.space
  /-- 元の標的の同じ段への右因子。 -/
  projection : level.space ⟶ (Y.level n).space
  /-- 元の射を厳密に回収する式。 -/
  fac : inclusion ≫ projection = f.app n
  /-- 右因子の全ての単射への RLP。 -/
  projection_rlp : (MorphismProperty.monomorphisms SSet.{u}).rlp projection.right

variable {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (n : ℕ)
  (s : SequentialBFArrowStage f n)

/-- 次段の相対 latching 対象から元の標的への実際の射。 -/
def sequentialBFArrowNextMap :
    pushout (PointedSimplicialSet.circle.{u} ◁ s.inclusion) (X.sigma n) ⟶
      (Y.level (n + 1)).space :=
  pushout.desc (PointedSimplicialSet.circle.{u} ◁ s.projection ≫ Y.sigma n)
    (f.app (n + 1)) (by
      rw [← Category.assoc, ← whiskerLeft_comp, s.fac, f.comm n])

/-- 相対 latching 対象からの境界分解により得られる次の実 Kan 段。 -/
def sequentialBFArrowNext : SequentialBFArrowStage f (n + 1) where
  level := ⟨PointedFactorization.middle (sequentialBFArrowNextMap f n s), inferInstance⟩
  inclusion := pushout.inr _ _ ≫ PointedFactorization.left (sequentialBFArrowNextMap f n s)
  projection := PointedFactorization.right (sequentialBFArrowNextMap f n s)
  fac := by
    rw [Category.assoc, PointedFactorization.fac]
    exact pushout.inr_desc _ _ _
  projection_rlp := PointedFactorization.right_rlp _

/-- 新しい前段の suspension から新しい次段への構造射。 -/
def sequentialBFArrowNextSigma :
    suspension s.level.space ⟶ (sequentialBFArrowNext f n s).level.space :=
  pushout.inl _ _ ≫ PointedFactorization.left (sequentialBFArrowNextMap f n s)

/-- 次の構造射は、元の BF 源の単射構造射を押し出した単射である。 -/
instance sequentialBFArrowNextSigma_mono : Mono (sequentialBFArrowNextSigma f n s).right := by
  let : Mono (X.sigma n).right := X.sigma_mono n
  let : Mono (pushout.inl (PointedSimplicialSet.circle.{u} ◁ s.inclusion) (X.sigma n)).right :=
    sequentialPointedPushout_inl_mono _ _
  change Mono ((pushout.inl (PointedSimplicialSet.circle.{u} ◁ s.inclusion) (X.sigma n)).right ≫
    (PointedFactorization.left (sequentialBFArrowNextMap f n s)).right)
  infer_instance

/-- 左因子は元の源の構造射と厳密に可換。 -/
lemma sequentialBFArrowNext_inclusion_comm :
    PointedSimplicialSet.circle.{u} ◁ s.inclusion ≫ sequentialBFArrowNextSigma f n s =
      X.sigma n ≫ (sequentialBFArrowNext f n s).inclusion := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ PointedFactorization.left (sequentialBFArrowNextMap f n s))
      (pushout.condition (f := PointedSimplicialSet.circle.{u} ◁ s.inclusion)
        (g := X.sigma n))).trans
        (Category.assoc _ _ _))

/-- 右因子は元の標的の構造射と厳密に可換。 -/
lemma sequentialBFArrowNext_projection_comm :
    PointedSimplicialSet.circle.{u} ◁ s.projection ≫ Y.sigma n =
      sequentialBFArrowNextSigma f n s ≫ (sequentialBFArrowNext f n s).projection := by
  change _ = (pushout.inl _ _ ≫ PointedFactorization.left _) ≫ PointedFactorization.right _
  rw [Category.assoc, PointedFactorization.fac]
  exact (pushout.inl_desc _ _ _).symm

end SerrePositivity.KST.NonConnective
