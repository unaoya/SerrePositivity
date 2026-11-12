module

public import SerrePositivity.HomologicalAlgebra.BarWeightEvaluation
import all SerrePositivity.HomologicalAlgebra.BarWeightEvaluation
import all SerrePositivity.HomologicalAlgebra.LinearWeightGenerators
import all SerrePositivity.HomologicalAlgebra.LinearFreeWeight
import all SerrePositivity.HomologicalAlgebra.LinearWeightRealization
import all SerrePositivity.HomologicalAlgebra.UnderNerveWeight
import all SerrePositivity.HomologicalAlgebra.UnderChainEquiv
import all SerrePositivity.HomologicalAlgebra.SimplicialReplacement

/-!
# bar 重みの coend と元の射列の余積の同型

## 概要
底の射列を恒等射で持ち上げ、その生成元を使って評価の逆を構成する。

## 方針
under 射列の標準持ち上げによる復元と coend の関係式で二つの合成を照合する。

## 規約
同型の両方向は元の生成元と元の構造射を保つ。

## 使われ方
HA 1.2.4。単体的置換の全複体と線形重みの全複体の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.HomologicalAlgebra
variable (A : Type u) [CommRing A] {J : Type} [SmallCategory J]

local instance : HasCoproducts.{0} (Complex A) := fun _ =>
  HomologicalComplex.instHasColimitsOfShape

/-- 元の射列の各因子を、恒等射での標準持ち上げの生成元へ送る。 -/
def barWeightEvaluationInv (X : J ⥤ Complex A) (n : SimplexCategoryᵒᵖ) :
    (simplicialReplacement X).obj n ⟶
      (linearWeightRealization A X).obj ((coefficientBarWeight J (𝟙_ (ModuleCat.{u} A))).obj n) :=
  Sigma.desc (fun s => barWeightGenerator A X n (s.obj 0) (underScaffold s))

/-- 逆射の元の各因子での公式。 -/
@[reassoc (attr := simp)]
theorem ι_barWeightEvaluationInv (X : J ⥤ Complex A) (n : SimplexCategoryᵒᵖ)
    (s : ComposableArrows J n.unop.len) :
    Sigma.ι (replacementTerms X n) s ≫ barWeightEvaluationInv A X n =
      barWeightGenerator A X n (s.obj 0) (underScaffold s) := Sigma.ι_comp_desc _ _

/-- 元の構造射で標準持ち上げを作用させると、元の under 射列の生成元に戻る。 -/
@[reassoc]
theorem barWeightGenerator_scaffold (X : J ⥤ Complex A) (n : SimplexCategoryᵒᵖ) (i : J)
    (τ : ComposableArrows (Under i) n.unop.len) :
    X.map (τ.obj 0).hom ≫ barWeightGenerator A X n ((τ.obj 0).right)
      (underScaffold (τ ⋙ Under.forget i)) = barWeightGenerator A X n i τ := by
  rw [barWeightGenerator_relation, underScaffold_factorization]

/-- 評価は各次数で、元の射列の余積への同じ指定同型になる。 -/
def barWeightEvaluationIso (X : J ⥤ Complex A) (n : SimplexCategoryᵒᵖ) :
    (linearWeightRealization A X).obj ((coefficientBarWeight J (𝟙_ (ModuleCat.{u} A))).obj n) ≅
      (simplicialReplacement X).obj n where
  hom := barWeightEvaluation A X n
  inv := barWeightEvaluationInv A X n
  hom_inv_id := by
    let W := (coefficientBarWeight J (𝟙_ (ModuleCat.{u} A))).obj n
    let B := (linearWeightBifunctor A X).obj W
    apply coend.hom_ext (F := B)
    intro i
    let Ti := weightTensorAt A X i
    let := weightTensorAt_preservesCoproducts A X i (ComposableArrows (Under i) n.unop.len)
    apply (cancel_epi (sigmaComparison Ti
      (fun _ : ComposableArrows (Under i) n.unop.len => 𝟙_ (ModuleCat.{u} A)))).mp
    apply Sigma.hom_ext
    intro τ
    simp only [ι_comp_sigmaComparison_assoc, barWeightEvaluation, coend.ι_desc_assoc]
    change (weightTensorAt A X i).map
      (coefficientBarWeightι J (𝟙_ (ModuleCat.{u} A)) n (op i) τ) ≫
      barWeightLeg A X n i ≫ barWeightEvaluationInv A X n = _
    rw [map_ι_barWeightLeg_assoc, ι_barWeightEvaluationInv]
    change (λ_ (X.obj i)).hom ≫ X.map (τ.obj 0).hom ≫
      barWeightGenerator A X n (τ.obj 0).right (underScaffold (τ ⋙ Under.forget i)) = _
    rw [barWeightGenerator_scaffold]
    change (λ_ (X.obj i)).hom ≫ (λ_ (X.obj i)).inv ≫
      Ti.map (coefficientBarWeightι J (𝟙_ (ModuleCat.{u} A)) n (op i) τ) ≫ coend.ι B i =
      Ti.map (coefficientBarWeightι J (𝟙_ (ModuleCat.{u} A)) n (op i) τ) ≫ coend.ι B i ≫ 𝟙 _
    rw [Iso.hom_inv_id_assoc, Category.comp_id]
  inv_hom_id := by
    apply Sigma.hom_ext
    intro s
    simp only [ι_barWeightEvaluationInv_assoc, barWeightGenerator_evaluation, underScaffold_forget]
    change X.map (𝟙 _ ≫ s.map (𝟙 _)) ≫ Sigma.ι (replacementTerms X n) s =
      Sigma.ι (replacementTerms X n) s ≫ 𝟙 _
    rw [s.map_id, Category.comp_id, X.map_id, Category.id_comp, Category.comp_id]

end SerrePositivity.HomologicalAlgebra
