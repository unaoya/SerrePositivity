module

public import SerrePositivity.HomologicalAlgebra.BarWeightRealizationNaturality
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.LinearWeightTotalComparison
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.ReplacementAugmentation
import all SerrePositivity.HomologicalAlgebra.BarWeightRealizationNaturality
import all SerrePositivity.HomologicalAlgebra.BarWeightEvaluationIso
import all SerrePositivity.HomologicalAlgebra.BarWeightEvaluation
import all SerrePositivity.HomologicalAlgebra.LinearWeightGenerators
import all SerrePositivity.HomologicalAlgebra.LinearCoYoneda
import all SerrePositivity.HomologicalAlgebra.LinearFreeWeight
import all SerrePositivity.HomologicalAlgebra.FreePresheafFunctor
import all SerrePositivity.HomologicalAlgebra.UnderChainEquiv
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.BarWeightComparison
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.UnderSourceVertex

/-!
# 単体的置換の増大と固定された重みの比較の照合

## 概要
先頭頂点単体による元の増大が、bar／標準重みの比較の coend の像と同じ射であることを示す。

## 方針
指定した評価同型の逆を前合成し、各底の射列の生成元で同じ単体作用素を計算する。

## 規約
擬同型性だけでなく、すでに定義した元の増大そのものと照合する。

## 使われ方
HA 1.2.4。bar の射列と単体次数による実現の同じ比較射。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicTopology
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
variable (A : Type u) [CommRing A]

local instance : HasCoproducts.{0} (Complex A) := fun _ =>
  HomologicalComplex.instHasColimitsOfShape
local instance : HasCoproducts.{u} (Complex A) := fun _ =>
  HomologicalComplex.instHasColimitsOfShape

/-- 恒等射での標準持ち上げの先頭頂点作用素は、元の同じ先頭頂点単体。 -/
@[simp]
theorem underSourceVertex_scaffold {n : ℕ}
    (s : ComposableArrows SimplexCategoryᵒᵖ n) :
    underSourceVertex (underScaffold s) = (sourceVertexSimplex s).op := by
  dsimp only [underSourceVertex]
  change (sourceVertexSimplex s ≫ (𝟙 _ ≫ s.map (𝟙 _)).unop).op = _
  rw [s.map_id, Category.comp_id, unop_id, Category.comp_id]

/-- 同じ余積因子での、線形重みの具体的な比較の公式。 -/
@[reassoc]
theorem coefficientBarWeightι_standardComparison (n : SimplexCategoryᵒᵖ)
    (i : SimplexCategoryᵒᵖ) (τ : ComposableArrows (Under i) n.unop.len) :
    coefficientBarWeightι _ (𝟙_ (ModuleCat.{u} A)) n (op i) τ ≫
        ((barStandardWeightComparison (𝟙_ (ModuleCat.{u} A))).app n).app (op i) =
      Sigma.ι (fun _ : i ⟶ n => 𝟙_ (ModuleCat.{u} A)) (underSourceVertex τ) := by
  simp [coefficientBarWeightι, barStandardWeightComparison, copowerFunctor]

/-- coend の比較の像は、元の単体的置換の同じ増大射。 -/
theorem barWeightComparison_evaluation (X : SimplicialObject (Complex A)) :
    Functor.whiskerRight (barStandardWeightComparison (𝟙_ (ModuleCat.{u} A)))
        (linearWeightRealization A X) ≫ (standardWeightRealizationIso A X).hom =
      (barWeightRealizationIso A X).hom ≫ replacementAugmentation X := by
  apply (cancel_epi (barWeightRealizationIso A X).inv).mp
  apply NatTrans.ext
  funext n
  apply Sigma.hom_ext
  intro s
  change Sigma.ι (replacementTerms X n) s ≫ barWeightEvaluationInv A X n ≫
      ((linearWeightRealization A X).map ((barStandardWeightComparison
        (𝟙_ (ModuleCat.{u} A))).app n) ≫ freeWeightEvaluation A X n) = _
  rw [ι_barWeightEvaluationInv_assoc]
  dsimp only [barWeightGenerator]
  rw [linearWeightGenerator_map_assoc, coefficientBarWeightι_standardComparison,
    underSourceVertex_scaffold]
  change freeWeightGenerator A X n (s.obj 0) (sourceVertexSimplex s).op ≫
    freeWeightEvaluation A X n = _
  rw [freeWeightGenerator_evaluation]
  exact (ι_replacementAugmentation X n s).symm.trans
    (congrArg (fun q : simplicialReplacement X ⟶ X =>
      Sigma.ι (replacementTerms X n) s ≫ q.app n)
      (Iso.inv_hom_id_assoc (barWeightRealizationIso A X) (replacementAugmentation X)).symm)

/-- bar 重みの鎖複体の coend の全複体を、元の単体的置換の直和全複体へ戻す同型。 -/
def barWeightTotalIso (X : SimplicialObject (Complex A)) :
    (linearWeightTotalFunctor A X).obj
      (coefficientBarWeightResolution SimplexCategoryᵒᵖ (𝟙_ (ModuleCat.{u} A))).complex ≅
      (directSumTotalFunctor A).obj (simplicialReplacement X) :=
  (chainTotalizationFunctor (ModuleCat.{u} A)).mapIso
    ((alternatingFaceMapComplexCompMapHomologicalComplexIso
      (linearWeightRealization A X)).app _ ≪≫
        (alternatingFaceMapComplex (Complex A)).mapIso (barWeightRealizationIso A X))

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
