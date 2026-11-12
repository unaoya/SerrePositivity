module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableSpanPushout
public import SerrePositivity.KST.SConstruction.GappedCofibers

/-! # 安定な標的の関手圏と gapped 図式の全押し出し
概要：全 span の点ごとの余極限の存在を供給し、一般の押し出しの判定と gapped 包含の保存を得る。
方針：既存の点ごとの判定と包含の余極限比較に安定性からの存在を適用する。
規約：零角つきの四角形に制限しない。使われ方：McCarthy 法の gapped 図式の押し出し。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：安定な標的の関手圏の任意 span は点ごとに余極限を持つ。
方針：各評価図式に全 span の余極限の存在を適用する。
規約：パラメーター A は任意。使われ方：点ごとの押し出し判定の存在条件。 -/
lemma functor_span_hasPointwiseColimits {A C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (p : (horn 2 0 : SSet.{u}) ⟶ (ihom A).obj C) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasPointwiseColimits p :=
  fun a => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_hasColimit_span (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.evaluateFunctorDiagram p a)

/-- 概要：安定な標的の関手圏の全押し出しは点ごとに判定できる。
方針：任意 span の点ごとの余極限の存在を既存の判定へ渡す。
規約：零角や点ごとの存在を追加仮定にしない。使われ方：coherent な押し出しの族。 -/
lemma functor_pushout_iff_pointwise {A C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ (ihom A).obj C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F ↔ ∀ a : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isPushoutSquare_iff_pointwise_of_hasPointwiseColimits F
    (functor_span_hasPointwiseColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan F))

/-- 概要：gapped 包含は任意の四角形の押し出し性を保ち反映する。
方針：全 span の点ごとの存在を gapped 包含の余錐比較に適用する。
規約：四角形に零角を要求しない。使われ方：gapped 図式の普遍的な押し出しの比較。 -/
lemma gappedInclusion_pushout_iff {n : ℕ} {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ sConstruction n C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (F ≫ (gappedSubcomplex n C).ι) := by
  have h := isColimitCone_gappedInclusion_iff_of_hasPointwiseColimits
    (functor_span_hasPointwiseColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan F ≫ (gappedSubcomplex n C).ι))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone F)
  apply h.trans
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isColimitCone_iff_of_val_eq _ _ (Category.assoc _ _ _)

/-- 概要：gapped 包含は零対象と全押し出しを保存する。
方針：既存の零対象保存と任意四角形の比較を組にする。
規約：既存の強い保存条件で述べる。使われ方：McCarthy 法の図式の包含。 -/
lemma gappedInclusion_preservesSConstructionData (n : ℕ) (C : SSet.{u})
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] : PreservesSConstructionData (gappedSubcomplex n C).ι :=
  ⟨fun _ hz => gappedInclusion_isZeroVertex n hz,
    fun F hF => (gappedInclusion_pushout_iff F).1 hF⟩

/-- 概要：gapped 図式の任意の押し出しは Ar[n] の全点で判定できる。
方針：包含による判定と関手圏の点ごとの判定を合成する。
規約：零角つき cofiber の場合に限定しない。使われ方：S の単体的構造と pushout の両立。 -/
lemma gappedInclusion_pushout_iff_pointwise {n : ℕ} {C : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ sConstruction n C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F ↔ ∀ a : (arNerve n) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (F ≫ (gappedSubcomplex n C).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a) :=
  (gappedInclusion_pushout_iff F).trans (functor_pushout_iff_pointwise _)

end SerrePositivity.KST.SConstruction
