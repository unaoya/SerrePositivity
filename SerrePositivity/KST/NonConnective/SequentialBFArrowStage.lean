module

public import SerrePositivity.KST.NonConnective.SequentialBFKanArrowStage

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

/-- 概要：指定された元の BF 射の一段の相対分解。
方針：同じ実段を一般化された Kan 列版から取り出す。
規約：既存の BF 型と段の厳密な射を保持する。
使われ方：K-B-S2 の一般化から旧 API への特殊化。 -/
structure SequentialBFArrowStage {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (n : ℕ) where
  /-- 概要：新しい点つき Kan 段。
方針：同じ実段を一般化された Kan 列版から取り出す。
規約：既存の BF 型と段の厳密な射を保持する。
使われ方：K-B-S2 の一般化から旧 API への特殊化。 -/
  level : PointedKanComplex.{u}
  /-- 概要：元の源の同じ段からの左因子。
方針：同じ実段を一般化された Kan 列版から取り出す。
規約：既存の BF 型と段の厳密な射を保持する。
使われ方：K-B-S2 の一般化から旧 API への特殊化。 -/
  inclusion : (X.level n).space ⟶ level.space
  /-- 概要：元の標的の同じ段への右因子。
方針：同じ実段を一般化された Kan 列版から取り出す。
規約：既存の BF 型と段の厳密な射を保持する。
使われ方：K-B-S2 の一般化から旧 API への特殊化。 -/
  projection : level.space ⟶ (Y.level n).space
  /-- 概要：元の射を厳密に回収する式。
方針：同じ実段を一般化された Kan 列版から取り出す。
規約：既存の BF 型と段の厳密な射を保持する。
使われ方：K-B-S2 の一般化から旧 API への特殊化。 -/
  fac : inclusion ≫ projection = f.app n
  /-- 概要：右因子の全ての単射への RLP。
方針：同じ実段を一般化された Kan 列版から取り出す。
規約：既存の BF 型と段の厳密な射を保持する。
使われ方：K-B-S2 の一般化から旧 API への特殊化。 -/
  projection_rlp : (MorphismProperty.monomorphisms SSet.{u}).rlp projection.right

/-- 概要：元の BF 射を同じ段と構造射の Kan 列の厳密射として読む。
方針：同じ実段を一般化された Kan 列版から取り出す。
規約：既存の BF 型と段の厳密な射を保持する。
使われ方：K-B-S2 の一般化から旧 API への特殊化。 -/
def sequentialBFArrowToKanHom {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) :
    KanSequence.Hom X.toKanSequence Y.toKanSequence where
  app := f.app
  comm := f.comm

/-- 概要：旧段データを一般化された同じ実段へ移す。
方針：同じ実段を一般化された Kan 列版から取り出す。
規約：既存の BF 型と段の厳密な射を保持する。
使われ方：K-B-S2 の一般化から旧 API への特殊化。 -/
def SequentialBFArrowStage.toKanStage {X Y : OmegaSpectrum.{u}} {f : X ⟶ Y}
    {n : ℕ} (s : SequentialBFArrowStage f n) :
    SequentialBFKanArrowStage (sequentialBFArrowToKanHom f) n :=
  ⟨s.level, s.inclusion, s.projection, s.fac, s.projection_rlp⟩

/-- 概要：一般化された同じ段データを旧構造体へ戻す。
方針：同じ実段を一般化された Kan 列版から取り出す。
規約：既存の BF 型と段の厳密な射を保持する。
使われ方：K-B-S2 の一般化から旧 API への特殊化。 -/
def sequentialBFArrowStageOfKan {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (n : ℕ)
    (s : SequentialBFKanArrowStage (sequentialBFArrowToKanHom f) n) :
    SequentialBFArrowStage f n :=
  ⟨s.level, s.inclusion, s.projection, s.fac, s.projection_rlp⟩

variable {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (n : ℕ)
  (s : SequentialBFArrowStage f n)

/-- 概要：旧 BF 標的への次段写像を一般の Kan 列版へ特殊化する。
方針：同じ実段を一般化された Kan 列版から取り出す。
規約：既存の BF 型と段の厳密な射を保持する。
使われ方：K-B-S2 の一般化から旧 API への特殊化。 -/
def sequentialBFArrowNextMap :
    pushout (PointedSimplicialSet.circle.{u} ◁ s.inclusion) (X.sigma n) ⟶
      (Y.level (n + 1)).space :=
  sequentialBFKanArrowNextMap (sequentialBFArrowToKanHom f) n s.toKanStage

/-- 概要：同じ相対分解の次段を旧構造体へ戻す。
方針：同じ実段を一般化された Kan 列版から取り出す。
規約：既存の BF 型と段の厳密な射を保持する。
使われ方：K-B-S2 の一般化から旧 API への特殊化。 -/
def sequentialBFArrowNext : SequentialBFArrowStage f (n + 1) :=
  sequentialBFArrowStageOfKan f (n + 1)
    (sequentialBFKanArrowNext (sequentialBFArrowToKanHom f) n s.toKanStage)

/-- 概要：旧版の構造射は同じ一般化された構造射そのもの。
方針：同じ実段を一般化された Kan 列版から取り出す。
規約：既存の BF 型と段の厳密な射を保持する。
使われ方：K-B-S2 の一般化から旧 API への特殊化。 -/
def sequentialBFArrowNextSigma :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension s.level.space ⟶ (sequentialBFArrowNext f n s).level.space :=
  sequentialBFKanArrowNextSigma (sequentialBFArrowToKanHom f) n s.toKanStage

/-- 概要：同じ次段構造射の単射性は一般化された実構成から従う。
方針：同じ実段を一般化された Kan 列版から取り出す。
規約：既存の BF 型と段の厳密な射を保持する。
使われ方：K-B-S2 の一般化から旧 API への特殊化。 -/
instance sequentialBFArrowNextSigma_mono : Mono (sequentialBFArrowNextSigma f n s).right :=
  sequentialBFKanArrowNextSigma_mono (sequentialBFArrowToKanHom f) n s.toKanStage

/-- 概要：同じ左因子の構造射との厳密可換式を旧版へ戻す。
方針：同じ実段を一般化された Kan 列版から取り出す。
規約：既存の BF 型と段の厳密な射を保持する。
使われ方：K-B-S2 の一般化から旧 API への特殊化。 -/
lemma sequentialBFArrowNext_inclusion_comm :
    PointedSimplicialSet.circle.{u} ◁ s.inclusion ≫ sequentialBFArrowNextSigma f n s =
      X.sigma n ≫ (sequentialBFArrowNext f n s).inclusion :=
  sequentialBFKanArrowNext_inclusion_comm (sequentialBFArrowToKanHom f) n s.toKanStage

/-- 概要：同じ右因子の構造射との厳密可換式を旧版へ戻す。
方針：同じ実段を一般化された Kan 列版から取り出す。
規約：既存の BF 型と段の厳密な射を保持する。
使われ方：K-B-S2 の一般化から旧 API への特殊化。 -/
lemma sequentialBFArrowNext_projection_comm :
    PointedSimplicialSet.circle.{u} ◁ s.projection ≫ Y.sigma n =
      sequentialBFArrowNextSigma f n s ≫ (sequentialBFArrowNext f n s).projection :=
  sequentialBFKanArrowNext_projection_comm (sequentialBFArrowToKanHom f) n s.toKanStage

end SerrePositivity.KST.NonConnective
