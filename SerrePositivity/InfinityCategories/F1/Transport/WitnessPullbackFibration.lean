module

public import SerrePositivity.InfinityCategories.F1.Transport.WitnessPullbackSymmetry
public import SerrePositivity.InfinityCategories.F1.Transport.WitnessInnerAnodyne
public import SerrePositivity.InfinityCategories.F1.Transport.WitnessRestrictionFibration

/-!
概要：降下の第一射影モデルで表現の制限の充填性を回収する。
方針：従来の制限を pullback の対称同型と合成する。
規約：モデル構造の仮定を加えない。
使われ方：セルの貼り合わせと骨格列での Kan fibration 条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories

local instance pullbackPreArrowMkLeftFibration {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p] :
    LeftFibration (Arrow.mk p).hom := by simpa only [Arrow.mk_hom]

local instance pullbackPreFstLeftFibration {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (g : D ⟶ B) : LeftFibration (pullback.fst g p) :=
  ⟨leftFibrations.pullback_fst g p (LeftFibration.mem (p := p))⟩

/-- 概要：単射による標準底変換の表現の前合成は Kan fibration。
方針：既存の制限の Kan fibration と対称同型の合成として証明する。
規約：単射以外の追加仮定は不要。
使われ方：降下でのセルと骨格の制限射。 -/
lemma transportWitnessPullbackPre_fibration {E B D : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] (g : D ⟶ B) [Mono g] :
    Fibration (transportWitnessPre (transportPullbackSquare p g)
      (transportPullbackSquare_isPullback p g)) := by
  rw [← transportWitnessRestriction_pullbackSymmetry]
  have := transportWitnessRestriction_fibration p g
  infer_instance

/-- 概要：inner anodyne 底変換の表現の前合成は trivial Kan fibration。
方針：既存の制限の全境界充填を対称同型との合成で保つ。
規約：非空性やモデル構造を仮定しない。
使われ方：標準単体を内ホーンから復元する帰納法。 -/
lemma transportWitnessPullbackPre_trivialKanFibration {E B D : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] (g : D ⟶ B)
    (hg : innerAnodyneExtensions g) :
    TrivialKanFibration (transportWitnessPre (transportPullbackSquare p g)
      (transportPullbackSquare_isPullback p g)) := by
  rw [← transportWitnessRestriction_pullbackSymmetry]
  exact ⟨trivialKanFibrations.comp_mem _ _
    (transportWitnessRestriction_trivialKanFibration_of_innerAnodyne p g hg).mem
    (MorphismProperty.rlp_of_isIso _ _)⟩

end SerrePositivity.InfinityCategories
