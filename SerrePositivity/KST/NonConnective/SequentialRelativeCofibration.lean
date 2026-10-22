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
