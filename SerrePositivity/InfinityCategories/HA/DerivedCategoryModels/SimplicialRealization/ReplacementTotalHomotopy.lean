module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.ReplacementWeightComparison
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.ReplacementWeightComparison
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.BarWeightComparison

/-!
# 元の単体的置換の増大の非有界全複体の鎖ホモトピー同値

## 概要
線形重みの比較を指定同型で戻し、元の増大そのものの鎖ホモトピー同値を得る。

## 方針
交代面複体と加法関手の自然同型の正方形を使い、同じ前向きの射を照合する。

## 規約
内部次数は非有界でよく、前向きの射を任意に取り替えない。

## 使われ方
HA 1.2.4。射列と単体次数の実現の比較。native 余錐との接続は別に行う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology
open scoped _root_.Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
variable (A : Type u) [CommRing A]

local instance : HasCoproducts.{0} (Complex A) := fun _ =>
  HomologicalComplex.instHasColimitsOfShape
local instance : HasCoproducts.{u} (Complex A) := fun _ =>
  HomologicalComplex.instHasColimitsOfShape

/-- 同じ重み比較を coend に移し、交代面複体の標準同型で戻した鎖ホモトピー同値。 -/
def realizedWeightComparisonHomotopyEquiv (X : SimplicialObject (Complex A)) :
    HomotopyEquiv
      ((alternatingFaceMapComplex _).obj
        (coefficientBarWeight _ (𝟙_ (ModuleCat.{u} A)) ⋙ linearWeightRealization A X))
      ((alternatingFaceMapComplex _).obj
        (standardSimplexWeight (𝟙_ (ModuleCat.{u} A)) ⋙ linearWeightRealization A X)) :=
  let e := alternatingFaceMapComplexCompMapHomologicalComplexIso (linearWeightRealization A X)
  (HomotopyEquiv.ofIso (e.app _).symm).trans
    (((linearWeightRealization A X).mapHomotopyEquiv
      (barStandardWeightHomotopyEquiv (𝟙_ (ModuleCat.{u} A)))).trans
        (HomotopyEquiv.ofIso (e.app _)))

/-- 前向きの射は、元の具体的な線形重みの比較の像そのもの。 -/
theorem realizedWeightComparisonHomotopyEquiv_hom (X : SimplicialObject (Complex A)) :
    (realizedWeightComparisonHomotopyEquiv A X).hom =
      (alternatingFaceMapComplex _).map
        (Functor.whiskerRight (barStandardWeightComparison (𝟙_ (ModuleCat.{u} A)))
          (linearWeightRealization A X)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  change 𝟙 _ ≫ (linearWeightRealization A X).map
      ((barStandardWeightComparison (𝟙_ (ModuleCat.{u} A))).app (Opposite.op ⦋n⦌)) ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]
  rfl

/-- 元の単体的置換の増大を前向きの射に持つ、交代面複体の鎖ホモトピー同値。 -/
def replacementAugmentationChainHomotopyEquiv (X : SimplicialObject (Complex A)) :
    HomotopyEquiv ((alternatingFaceMapComplex _).obj (simplicialReplacement X))
      ((alternatingFaceMapComplex _).obj X) :=
  (HomotopyEquiv.ofIso ((alternatingFaceMapComplex _).mapIso (barWeightRealizationIso A X).symm)).trans
    ((realizedWeightComparisonHomotopyEquiv A X).trans
      (HomotopyEquiv.ofIso ((alternatingFaceMapComplex _).mapIso (standardWeightRealizationIso A X))))

/-- 同じ鎖ホモトピー同値の前向きの射と、既存の増大の射との厳密な一致。 -/
theorem replacementAugmentationChainHomotopyEquiv_hom (X : SimplicialObject (Complex A)) :
    (replacementAugmentationChainHomotopyEquiv A X).hom =
      (alternatingFaceMapComplex _).map (replacementAugmentation X) := by
  change (alternatingFaceMapComplex _).map (barWeightRealizationIso A X).inv ≫
    (realizedWeightComparisonHomotopyEquiv A X).hom ≫
    (alternatingFaceMapComplex _).map (standardWeightRealizationIso A X).hom = _
  rw [realizedWeightComparisonHomotopyEquiv_hom, ← Functor.map_comp,
    barWeightComparison_evaluation, ← Functor.map_comp, Iso.inv_hom_id_assoc]

/-- 非有界係数でも元の増大を直和全複体へ送った射は鎖ホモトピー同値。 -/
def replacementAugmentationTotalHomotopyEquiv (X : SimplicialObject (Complex A)) :
    HomotopyEquiv ((directSumTotalFunctor A).obj (simplicialReplacement X))
      ((directSumTotalFunctor A).obj X) :=
  chainTotalizationHomotopyEquiv (ModuleCat.{u} A) (replacementAugmentationChainHomotopyEquiv A X)

/-- 全複体の同じ前向きの射は、既存の増大の像。 -/
theorem replacementAugmentationTotalHomotopyEquiv_hom (X : SimplicialObject (Complex A)) :
    (replacementAugmentationTotalHomotopyEquiv A X).hom =
      (directSumTotalFunctor A).map (replacementAugmentation X) := by
  exact congrArg ((chainTotalizationFunctor (ModuleCat.{u} A)).map)
    (replacementAugmentationChainHomotopyEquiv_hom A X)

/-- 元の増大の実際の全複体の射は擬同型。 -/
instance replacementAugmentationTotal_quasiIso (X : SimplicialObject (Complex A)) :
    QuasiIso ((directSumTotalFunctor A).map (replacementAugmentation X)) := by
  rw [← replacementAugmentationTotalHomotopyEquiv_hom]
  infer_instance

/-- 元の全図式・全射で自然な、単体的置換の実現から元の実現への同じ増大。 -/
def replacementTotalAugmentationNatTrans :
    simplicialReplacementFunctor (J := SimplexCategoryᵒᵖ) (C := Complex A) ⋙
        directSumTotalFunctor A ⟶ directSumTotalFunctor A :=
  Functor.whiskerRight replacementAugmentationNatTrans (directSumTotalFunctor A)

/-- 全関手の自然比較の各成分も、同じ増大の擬同型である。 -/
instance replacementTotalAugmentationNatTrans_quasiIso (X : SimplicialObject (Complex A)) :
    QuasiIso ((replacementTotalAugmentationNatTrans A).app X) :=
  inferInstanceAs (QuasiIso ((directSumTotalFunctor A).map (replacementAugmentation X)))

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
