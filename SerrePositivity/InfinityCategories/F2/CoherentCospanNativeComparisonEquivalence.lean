module

public import SerrePositivity.InfinityCategories.F2.CoherentCospanCommonBaseCompatibility

/-!
概要：各点の native 錐の極限性から、元の native 引き戻し比較の弱同値性を証明する。
方針：底で整合する指定二脚を貼り、模型比較の同値性を移して共通の後合成を消去する。
規約：元の比較射と指定 path を保持。使われ方：一般 coherent filtered 図式の交換。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}} [Quasicategory B]
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z)
local notation "p" => intervalReplacementEndpoint
  (continuousKanReplacement.map (coherentTransformationTotalMap X Z C.fromLeft))
local notation "q" => intervalReplacementEndpoint
  (continuousKanReplacement.map (coherentTransformationTotalMap Y Z C.fromRight))
local instance : KanComplex (pullback p q) :=
  HomotopyLimits.pullback_kanComplex_of_fibration _ _

/-- 同じ二脚と指定底の整合から、共通の引き戻し内の全体の比較同型を貼る。 -/
def coherentCospanCommonComparisonIso :
    FunctorIso (coherentCospanNativeCommonComparison F X Y Z C)
      (coherentCospanModelCommonComparison F X Y Z C) :=
  Classical.choice (strictPullback_functorIso_exists p q
    (coherentCospanNativeCommonComparison F X Y Z C)
    (coherentCospanModelCommonComparison F X Y Z C)
    (coherentCospanCommonLeftIso F X Y Z C) (coherentCospanCommonRightIso F X Y Z C)
    (coherentCospanCommonBaseCompatibility F X Y Z C))

/-- 各点の極限性から、共通の引き戻しへの native 合成比較もホモトピー同値。 -/
lemma coherentCospanNativeCommonComparison_homotopyEquivalence [IsFilteredInfinity B]
    (hc : ∀ b, IsLimitCone (coherentCospanConePointwiseCone F X Y Z C b)) :
    IsSimplicialHomotopyEquivalence (coherentCospanNativeCommonComparison F X Y Z C) := by
  have hm := coherentCospanModelCommonComparison_homotopyEquivalence F X Y Z C hc
  exact (hm.isQCatEquivalence.ofFunctorIso
    (coherentCospanCommonComparisonIso F X Y Z C).symm).isSimplicialHomotopyEquivalence

/-- 元の native 比較候補そのものに、単体的ホモトピー逆が存在する。 -/
lemma coherentCospanConeNativeComparison_homotopyEquivalence [IsFilteredInfinity B]
    (hc : ∀ b, IsLimitCone (coherentCospanConePointwiseCone F X Y Z C b)) :
    IsSimplicialHomotopyEquivalence (coherentCospanConeNativeComparison F X Y Z C) := by
  exact (coherentCospanNativeKanPullbackComparison_homotopyEquivalence F X Y Z C).cancel_right
    (coherentCospanNativeCommonComparison_homotopyEquivalence F X Y Z C hc)

/-- 各点の元の native 錐が極限なら、元の native 比較候補は弱同値である。 -/
lemma coherentCospanConeNativeComparison_isWeakHomotopyEquivalence [IsFilteredInfinity B]
    (hc : ∀ b, IsLimitCone (coherentCospanConePointwiseCone F X Y Z C b)) :
    IsWeakHomotopyEquivalence (coherentCospanConeNativeComparison F X Y Z C) :=
  (coherentCospanConeNativeComparison_homotopyEquivalence F X Y Z C hc).isWeakHomotopyEquivalence

end SerrePositivity.InfinityCategories.F2
