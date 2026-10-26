module

public import SerrePositivity.KST.NonConnective.SequentialBFArrowFactorization

/-!
概要：BF 射の相対 latching 単射条件と、実分解の左因子の検証。
方針：指定された元の構造正方形の押し出しから次段への射を使う。
規約：モデル圏の instance を導入せず、単射の具体的な性質として定義する。
使われ方：逐次置換の全反変 Hom の fibration 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective

/-- 元の BF 射の構造正方形における、相対 latching 対象から次段への実射。 -/
def sequentialRelativeLatchingMap {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    pushout (PointedSimplicialSet.circle.{u} ◁ f.app n) (X.sigma n) ⟶ (Y.level (n + 1)).space :=
  pushout.desc (Y.sigma n) (f.app (n + 1)) (f.comm n)

/-- BF 射の零段と全ての相対 latching 射が単射であるという具体的な条件。 -/
def IsSequentialRelativeCofibration {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) : Prop :=
  Mono (f.app 0).right ∧ ∀ n, Mono (sequentialRelativeLatchingMap f n).right

/-- 概要：一般 Kan 標的への分解の相対 latching 射は同じ実境界分解の左因子。
方針：元の構造正方形の押し出しを一般構成の回収式へ読み替える。
規約：標的の構造射の単射性を使わない。
使われ方：K-B-S2 の左因子を既存の相対 cofibration 条件へ接続する。 -/
lemma sequentialBFKanArrowLeft_relativeLatching
    {X : OmegaSpectrum.{u}} {Y : KanSequence.{u}}
    (f : KanSequence.Hom X.toKanSequence Y) (hY : Y.OmegaCondition) (n : ℕ) :
    sequentialRelativeLatchingMap (sequentialBFKanArrowLeft f hY) n =
      PointedFactorization.left
        (sequentialBFKanArrowNextMap f n (sequentialBFKanArrowStage f n)) :=
  sequentialBFKanArrowLeft_latching f hY n

/-- 概要：一般 Kan 標的への実分解の左因子は全段で相対 cofibration 条件を満たす。
方針：同じ零段単射と全相対 latching 単射を元の定義へ代入する。
規約：標的の Ω 条件は明示証明としてだけ使う。
使われ方：Sp 向けの K-B-S2 公開相対分解界面。 -/
lemma sequentialBFKanArrowLeft_isRelativeCofibration
    {X : OmegaSpectrum.{u}} {Y : KanSequence.{u}}
    (f : KanSequence.Hom X.toKanSequence Y) (hY : Y.OmegaCondition) :
    IsSequentialRelativeCofibration (sequentialBFKanArrowLeft f hY) :=
  ⟨sequentialBFKanArrowLeft_zero_mono f hY,
    fun n => sequentialBFKanArrowLeft_latching_mono f hY n⟩

/-- 構成した左因子の相対 latching 射は、元の境界分解の左因子そのもの。 -/
lemma sequentialBFArrowLeft_latching {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    sequentialRelativeLatchingMap (sequentialBFArrowLeft f) n =
      PointedFactorization.left (sequentialBFArrowNextMap f n (sequentialBFArrowStage f n)) := by
  change pushout.desc
    (pushout.inl _ _ ≫ PointedFactorization.left _)
    (pushout.inr _ _ ≫ PointedFactorization.left _) _ = _
  apply pushout.hom_ext
  · exact pushout.inl_desc _ _ _
  · exact pushout.inr_desc _ _ _

/-- 任意の BF 射の実分解の左因子は、全段で相対 latching 単射条件を満たす。 -/
lemma sequentialBFArrowLeft_isRelativeCofibration {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) :
    IsSequentialRelativeCofibration (sequentialBFArrowLeft f) := by
  refine ⟨sequentialBFArrowLeft_zero_mono f, ?_⟩
  intro n
  rw [sequentialBFArrowLeft_latching]
  infer_instance

end SerrePositivity.KST.NonConnective
