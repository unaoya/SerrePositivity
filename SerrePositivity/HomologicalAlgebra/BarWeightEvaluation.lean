module

public import SerrePositivity.HomologicalAlgebra.LinearWeightGenerators
public import SerrePositivity.HomologicalAlgebra.UnderNerveWeight
public import SerrePositivity.HomologicalAlgebra.UnderChainEquiv
public import SerrePositivity.HomologicalAlgebra.SimplicialReplacement
import all SerrePositivity.HomologicalAlgebra.LinearWeightGenerators
import all SerrePositivity.HomologicalAlgebra.LinearFreeWeight
import all SerrePositivity.HomologicalAlgebra.LinearWeightRealization
import all SerrePositivity.HomologicalAlgebra.UnderNerveWeight
import all SerrePositivity.HomologicalAlgebra.UnderChainEquiv
import all SerrePositivity.HomologicalAlgebra.SimplicialReplacement

/-!
# bar 重みの coend の射列の余積への評価

## 概要
under 圏の射列で添字づけた重みを、元の底の射列の先頭の値へ評価する。

## 方針
各生成元に先頭の構造射を作用させ、coend の二つの作用を照合する。

## 規約
余積の添字も係数の射も、元の射列のものを保つ。

## 使われ方
HA 1.2.4。strict な図式の bar と単体的置換の具体的比較。
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

/-- 元の under 射列の同じ余積因子から、底の射列の同じ因子への射。 -/
def barWeightLeg (X : J ⥤ Complex A) (n : SimplexCategoryᵒᵖ) (i : J) :
    (weightTensorAt A X i).obj (((coefficientBarWeight J (𝟙_ (ModuleCat.{u} A))).obj n).obj (op i)) ⟶
      (simplicialReplacement X).obj n := by
  let T := weightTensorAt A X i
  let := weightTensorAt_preservesCoproducts A X i (ComposableArrows (Under i) n.unop.len)
  exact inv (sigmaComparison T (fun _ : ComposableArrows (Under i) n.unop.len =>
    𝟙_ (ModuleCat.{u} A))) ≫ Sigma.desc (fun τ =>
      (λ_ (X.obj i)).hom ≫ X.map (τ.obj 0).hom ≫
        Sigma.ι (replacementTerms X n) (τ ⋙ Under.forget i))

/-- 各指定生成元の評価は、先頭の構造射と元の底の射列の包含。 -/
@[reassoc]
theorem map_ι_barWeightLeg (X : J ⥤ Complex A) (n : SimplexCategoryᵒᵖ) (i : J)
    (τ : ComposableArrows (Under i) n.unop.len) :
    (weightTensorAt A X i).map (coefficientBarWeightι J (𝟙_ (ModuleCat.{u} A)) n (op i) τ) ≫
      barWeightLeg A X n i = (λ_ (X.obj i)).hom ≫ X.map (τ.obj 0).hom ≫
        Sigma.ι (replacementTerms X n) (τ ⋙ Under.forget i) := by
  let := weightTensorAt_preservesCoproducts A X i (ComposableArrows (Under i) n.unop.len)
  dsimp only [barWeightLeg, coefficientBarWeightι]
  simp only [map_ι_comp_inv_sigmaComparison_assoc, Sigma.ι_comp_desc]

/-- 各因子の評価は、同じ coend の二つの作用に両立する。 -/
theorem barWeightLeg_condition (X : J ⥤ Complex A) (n : SimplexCategoryᵒᵖ)
    {i k : J} (g : i ⟶ k) :
    (((linearWeightBifunctor A X).obj ((coefficientBarWeight J (𝟙_ (ModuleCat.{u} A))).obj n)).map
      g.op).app i ≫ barWeightLeg A X n i =
      (((linearWeightBifunctor A X).obj ((coefficientBarWeight J (𝟙_ (ModuleCat.{u} A))).obj n)).obj
        (op k)).map g ≫ barWeightLeg A X n k := by
  let Ti := weightTensorAt A X i
  let Tk := weightTensorAt A X k
  let W := (coefficientBarWeight J (𝟙_ (ModuleCat.{u} A))).obj n
  let B := (linearWeightBifunctor A X).obj W
  let := weightTensorAt_preservesCoproducts A X i (ComposableArrows (Under k) n.unop.len)
  apply (cancel_epi (sigmaComparison Ti
    (fun _ : ComposableArrows (Under k) n.unop.len => 𝟙_ (ModuleCat.{u} A)))).mp
  apply Sigma.hom_ext
  intro τ
  simp only [ι_comp_sigmaComparison_assoc]
  have he : Ti.map (coefficientBarWeightι J (𝟙_ (ModuleCat.{u} A)) n (op k) τ) ≫
      (B.obj (op k)).map g = (𝟙_ (Complex A) ◁ X.map g) ≫
        Tk.map (coefficientBarWeightι J (𝟙_ (ModuleCat.{u} A)) n (op k) τ) := by
    exact (whisker_exchange
      ((HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0).map
        (coefficientBarWeightι J (𝟙_ (ModuleCat.{u} A)) n (op k) τ)) (X.map g)).symm
  change Ti.map (coefficientBarWeightι J (𝟙_ (ModuleCat.{u} A)) n (op k) τ) ≫
    Ti.map (W.map g.op) ≫ barWeightLeg A X n i = _
  rw [← Ti.map_comp_assoc, coefficientBarWeightι_map, map_ι_barWeightLeg]
  change ((λ_ (X.obj i)).hom ≫ X.map (g ≫ (τ.obj 0).hom)) ≫
      Sigma.ι (replacementTerms X n) (τ ⋙ Under.forget k) =
    Ti.map (coefficientBarWeightι J (𝟙_ (ModuleCat.{u} A)) n (op k) τ) ≫
      (B.obj (op k)).map g ≫ barWeightLeg A X n k
  rw [← Category.assoc (Ti.map _), he]
  rw [Category.assoc (𝟙_ (Complex A) ◁ X.map g)]
  change _ = (𝟙_ (Complex A) ◁ X.map g) ≫
    (weightTensorAt A X k).map (coefficientBarWeightι J (𝟙_ (ModuleCat.{u} A)) n (op k) τ) ≫
      barWeightLeg A X n k
  rw [map_ι_barWeightLeg]
  rw [X.map_comp, Category.assoc]
  exact (leftUnitor_naturality_assoc (X.map g)
    (X.map (τ.obj 0).hom ≫ Sigma.ι (replacementTerms X n) (τ ⋙ Under.forget k))).symm

/-- bar 重みの同じ coend から、元の単体的置換の各次数への評価。 -/
def barWeightEvaluation (X : J ⥤ Complex A) (n : SimplexCategoryᵒᵖ) :
    (linearWeightRealization A X).obj ((coefficientBarWeight J (𝟙_ (ModuleCat.{u} A))).obj n) ⟶
      (simplicialReplacement X).obj n :=
  coend.desc (barWeightLeg A X n) (fun _ _ g => barWeightLeg_condition A X n g)

/-- 元の under 射列に対応する coend の生成元。 -/
def barWeightGenerator (X : J ⥤ Complex A) (n : SimplexCategoryᵒᵖ) (i : J)
    (τ : ComposableArrows (Under i) n.unop.len) :=
  linearWeightGenerator A X ((coefficientBarWeight J (𝟙_ (ModuleCat.{u} A))).obj n) i
    (coefficientBarWeightι J (𝟙_ (ModuleCat.{u} A)) n (op i) τ)

/-- 同じ生成元の像は、構造射の後の底の射列の包含。 -/
@[reassoc (attr := simp)]
theorem barWeightGenerator_evaluation (X : J ⥤ Complex A) (n : SimplexCategoryᵒᵖ) (i : J)
    (τ : ComposableArrows (Under i) n.unop.len) :
    barWeightGenerator A X n i τ ≫ barWeightEvaluation A X n =
      X.map (τ.obj 0).hom ≫ Sigma.ι (replacementTerms X n) (τ ⋙ Under.forget i) := by
  dsimp only [barWeightGenerator, linearWeightGenerator, barWeightEvaluation]
  simp only [Category.assoc, coend.ι_desc, map_ι_barWeightLeg, Iso.inv_hom_id_assoc]

/-- 元の添字の射と under 射列の前合成は、同じ coend の生成元で両立する。 -/
@[reassoc]
theorem barWeightGenerator_relation (X : J ⥤ Complex A) (n : SimplexCategoryᵒᵖ)
    {i k : J} (g : i ⟶ k) (τ : ComposableArrows (Under k) n.unop.len) :
    X.map g ≫ barWeightGenerator A X n k τ =
      barWeightGenerator A X n i (τ ⋙ Under.map g) := by
  dsimp only [barWeightGenerator]
  rw [linearWeightGenerator_relation, coefficientBarWeightι_map]
  rfl

end SerrePositivity.HomologicalAlgebra
