module
public import SerrePositivity.KST.Spectra.KanSequence

public import SerrePositivity.KST.NonConnective.SequentialPointedPushoutMono
public import SerrePositivity.KST.Spectra.PointedFactorization

/-!
概要：BF 源から任意の Kan 列への射を構造射に沿って相対分解する一段の実データ。
方針：既存の源と新しい前段の suspension を押し出し、元の標的への射を境界分解する。
規約：源だけが BF 対象。標的は Kan 列でよく、その Ω 条件や構造射の単射性を使わない。
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

/-- 概要：指定された元の BF 射の一段の相対分解。
方針：同じ相対 latching 押し出しと境界分解を使う。
規約：標的 Kan 列の Ω 条件を要求しない。
使われ方：K-B-S2 の逐次 BF 相対分解。 -/
structure SequentialBFKanArrowStage {X : OmegaSpectrum.{u}} {Y : KanSequence.{u}}
    (f : KanSequence.Hom X.toKanSequence Y) (n : ℕ) where
  /-- 概要：新しい点つき Kan 段。
方針：同じ相対 latching 押し出しと境界分解を使う。
規約：標的 Kan 列の Ω 条件を要求しない。
使われ方：K-B-S2 の逐次 BF 相対分解。 -/
  level : PointedKanComplex.{u}
  /-- 概要：元の源の同じ段からの左因子。
方針：同じ相対 latching 押し出しと境界分解を使う。
規約：標的 Kan 列の Ω 条件を要求しない。
使われ方：K-B-S2 の逐次 BF 相対分解。 -/
  inclusion : (X.level n).space ⟶ level.space
  /-- 概要：元の標的の同じ段への右因子。
方針：同じ相対 latching 押し出しと境界分解を使う。
規約：標的 Kan 列の Ω 条件を要求しない。
使われ方：K-B-S2 の逐次 BF 相対分解。 -/
  projection : level.space ⟶ (Y.level n).space
  /-- 概要：元の射を厳密に回収する式。
方針：同じ相対 latching 押し出しと境界分解を使う。
規約：標的 Kan 列の Ω 条件を要求しない。
使われ方：K-B-S2 の逐次 BF 相対分解。 -/
  fac : inclusion ≫ projection = f.app n
  /-- 概要：右因子の全ての単射への RLP。
方針：同じ相対 latching 押し出しと境界分解を使う。
規約：標的 Kan 列の Ω 条件を要求しない。
使われ方：K-B-S2 の逐次 BF 相対分解。 -/
  projection_rlp : (MorphismProperty.monomorphisms SSet.{u}).rlp projection.right

variable {X : OmegaSpectrum.{u}} {Y : KanSequence.{u}}
    (f : KanSequence.Hom X.toKanSequence Y) (n : ℕ)
  (s : SequentialBFKanArrowStage f n)

/-- 概要：次段の相対 latching 対象から元の標的への実際の射。
方針：同じ相対 latching 押し出しと境界分解を使う。
規約：標的 Kan 列の Ω 条件を要求しない。
使われ方：K-B-S2 の逐次 BF 相対分解。 -/
def sequentialBFKanArrowNextMap :
    pushout (PointedSimplicialSet.circle.{u} ◁ s.inclusion) (X.sigma n) ⟶
      (Y.level (n + 1)).space :=
  pushout.desc (PointedSimplicialSet.circle.{u} ◁ s.projection ≫ Y.sigma n)
    (f.app (n + 1)) (by
      rw [← Category.assoc, ← whiskerLeft_comp, s.fac, f.comm n]
      rfl)

/-- 概要：相対 latching 対象からの境界分解により得られる次の実 Kan 段。
方針：同じ相対 latching 押し出しと境界分解を使う。
規約：標的 Kan 列の Ω 条件を要求しない。
使われ方：K-B-S2 の逐次 BF 相対分解。 -/
def sequentialBFKanArrowNext : SequentialBFKanArrowStage f (n + 1) where
  level := ⟨PointedFactorization.middle (sequentialBFKanArrowNextMap f n s), inferInstance⟩
  inclusion := pushout.inr _ _ ≫ PointedFactorization.left (sequentialBFKanArrowNextMap f n s)
  projection := PointedFactorization.right (sequentialBFKanArrowNextMap f n s)
  fac := by
    rw [Category.assoc, PointedFactorization.fac]
    exact pushout.inr_desc _ _ _
  projection_rlp := PointedFactorization.right_rlp _

/-- 概要：新しい前段の suspension から新しい次段への構造射。
方針：同じ相対 latching 押し出しと境界分解を使う。
規約：標的 Kan 列の Ω 条件を要求しない。
使われ方：K-B-S2 の逐次 BF 相対分解。 -/
def sequentialBFKanArrowNextSigma :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension s.level.space ⟶ (sequentialBFKanArrowNext f n s).level.space :=
  pushout.inl _ _ ≫ PointedFactorization.left (sequentialBFKanArrowNextMap f n s)

/-- 概要：次の構造射は、元の BF 源の単射構造射を押し出した単射である。
方針：同じ相対 latching 押し出しと境界分解を使う。
規約：標的 Kan 列の Ω 条件を要求しない。
使われ方：K-B-S2 の逐次 BF 相対分解。 -/
instance sequentialBFKanArrowNextSigma_mono : Mono (sequentialBFKanArrowNextSigma f n s).right := by
  let : Mono (X.sigma n).right := X.sigma_mono n
  let : Mono (pushout.inl (PointedSimplicialSet.circle.{u} ◁ s.inclusion) (X.sigma n)).right :=
    sequentialPointedPushout_inl_mono _ _
  change Mono ((pushout.inl (PointedSimplicialSet.circle.{u} ◁ s.inclusion) (X.sigma n)).right ≫
    (PointedFactorization.left (sequentialBFKanArrowNextMap f n s)).right)
  infer_instance

/-- 概要：左因子は元の源の構造射と厳密に可換。
方針：同じ相対 latching 押し出しと境界分解を使う。
規約：標的 Kan 列の Ω 条件を要求しない。
使われ方：K-B-S2 の逐次 BF 相対分解。 -/
lemma sequentialBFKanArrowNext_inclusion_comm :
    PointedSimplicialSet.circle.{u} ◁ s.inclusion ≫ sequentialBFKanArrowNextSigma f n s =
      X.sigma n ≫ (sequentialBFKanArrowNext f n s).inclusion := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ PointedFactorization.left (sequentialBFKanArrowNextMap f n s))
      (pushout.condition (f := PointedSimplicialSet.circle.{u} ◁ s.inclusion)
        (g := X.sigma n))).trans
        (Category.assoc _ _ _))

/-- 概要：右因子は元の標的の構造射と厳密に可換。
方針：同じ相対 latching 押し出しと境界分解を使う。
規約：標的 Kan 列の Ω 条件を要求しない。
使われ方：K-B-S2 の逐次 BF 相対分解。 -/
lemma sequentialBFKanArrowNext_projection_comm :
    PointedSimplicialSet.circle.{u} ◁ s.projection ≫ Y.sigma n =
      sequentialBFKanArrowNextSigma f n s ≫ (sequentialBFKanArrowNext f n s).projection := by
  change _ = (pushout.inl _ _ ≫ PointedFactorization.left _) ≫ PointedFactorization.right _
  rw [Category.assoc, PointedFactorization.fac]
  exact (pushout.inl_desc _ _ _).symm

end SerrePositivity.KST.NonConnective
