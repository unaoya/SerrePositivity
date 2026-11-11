module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InvertingPostcomposition

/-!
概要：局所化に沿う相対関手の制限を、同じ底上の全空間比較として構成する。
方針：反転関手圏への後合成を局所化の前合成で引き戻す。
規約：元の後合成と元の局所化前合成を両射影で厳密に回収する。
使われ方：全空間の同値から、元の指定底を保つ相対制限の同値を導く。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
variable {N A E B : SSet.{u}} (f : N ⟶ A) (W : Set (N _⦋1⦌))
  (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges f W) (p : E ⟶ B)

/-- 反転関手圏への後合成と局所化前合成の厳密な可換性。 -/
lemma localizationPrecomposition_postcomp :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition f W hf E ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.invertingFunctorPostcomp p W =
      (ihom A).map p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition f W hf B := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors N B W).ι).mp
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.invertingFunctorPostcomp_ι, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition_ι, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition_ι]
  exact ((pre f).naturality p).symm

/-- 指定した元の底関手を保持するための全空間。 -/
abbrev localizationRelativeTotal : SSet.{u} :=
  pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition f W hf B) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.invertingFunctorPostcomp p W)

/-- 元の全底関手圏への射影。 -/
def localizationRelativeProjection : localizationRelativeTotal f W hf p ⟶ (ihom A).obj B :=
  pullback.fst _ _

/-- 全底関手圏への射影は left fibration。 -/
instance localizationRelativeProjection_leftFibration [Quasicategory E] [Quasicategory B]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (localizationRelativeProjection f W hf p) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_fst _ _ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem⟩

/-- 元の全関手圏から、局所化後の指定底を保持する全空間への比較。 -/
def localizationRelativeTotalMap : (ihom A).obj E ⟶ localizationRelativeTotal f W hf p :=
  pullback.lift ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition f W hf E)
    (localizationPrecomposition_postcomp f W hf p).symm

/-- 比較射は元の後合成を厳密に保つ。 -/
lemma localizationRelativeTotalMap_projection :
    localizationRelativeTotalMap f W hf p ≫ localizationRelativeProjection f W hf p =
      (ihom A).map p := pullback.lift_fst _ _ _

/-- 比較射は元の局所化前合成を厳密に回収する。 -/
lemma localizationRelativeTotalMap_restriction :
    localizationRelativeTotalMap f W hf p ≫ pullback.snd
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition f W hf B) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.invertingFunctorPostcomp p W) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition f W hf E := pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
