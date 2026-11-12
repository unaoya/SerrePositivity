module

public import SerrePositivity.HomologicalAlgebra.LinearFreeWeight
import all SerrePositivity.HomologicalAlgebra.LinearFreeWeight
import all SerrePositivity.HomologicalAlgebra.LinearWeightRealization

/-!
# 自由線形重みの coend の評価同型

## 概要
自由表現可能重みの線形 coend を、元の図式の同じ値へ同一視する。

## 方針
元の生成元を図式の同じ射へ送り、恒等射の生成元から逆を作る。

## 規約
coend の標準包含と元の単位子を保持する。単なる存在同型ではない。

## 使われ方
HA 1.2.4、Weibel §2.2。標準単体重みの全複体を具体的な交代面全複体へ戻す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.HomologicalAlgebra
variable (A : Type u) [CommRing A] {J : Type} [SmallCategory J]

/-- 自由重みの coend から、元の図式の指定した値への同じ標準射。 -/
def freeWeightEvaluation (X : J ⥤ Complex A) (j : J) :
    (linearWeightRealization A X).obj (freeModuleWeight A j) ⟶ X.obj j :=
  coend.desc (freeWeightLeg A X j) (fun _ _ g => freeWeightLeg_condition A X j g)

/-- 自由重みの射 f に対応する、元の値から同じ coend への生成元の射。 -/
def freeWeightGenerator (X : J ⥤ Complex A) (j i : J) (f : i ⟶ j) :
    X.obj i ⟶ (linearWeightRealization A X).obj (freeModuleWeight A j) :=
  (λ_ (X.obj i)).inv ≫
    (weightTensorAt A X i).map (Sigma.ι (fun _ : i ⟶ j => 𝟙_ (ModuleCat.{u} A)) f) ≫
      coend.ι ((linearWeightBifunctor A X).obj (freeModuleWeight A j)) i

/-- 生成元の標準射の像は、元の同じ図式の射。 -/
@[reassoc (attr := simp)]
theorem freeWeightGenerator_evaluation (X : J ⥤ Complex A) (j i : J) (f : i ⟶ j) :
    freeWeightGenerator A X j i f ≫ freeWeightEvaluation A X j = X.map f := by
  simp [freeWeightGenerator, freeWeightEvaluation, Category.assoc, map_ι_freeWeightLeg]

/-- 恒等射の生成元への作用は、元の図式の同じ射に両立する。 -/
theorem freeWeightGenerator_relation (X : J ⥤ Complex A) (j i : J) (f : i ⟶ j) :
    X.map f ≫ freeWeightGenerator A X j j (𝟙 j) = freeWeightGenerator A X j i f := by
  let B := (linearWeightBifunctor A X).obj (freeModuleWeight A j)
  let Ti := weightTensorAt A X i
  let Tj := weightTensorAt A X j
  let U := 𝟙_ (ModuleCat.{u} A)
  have he : Ti.map (Sigma.ι (fun _ : j ⟶ j => U) (𝟙 j)) ≫ (B.obj (op j)).map f =
      (𝟙_ (Complex A) ◁ X.map f) ≫ Tj.map (Sigma.ι (fun _ : j ⟶ j => U) (𝟙 j)) := by
    exact (whisker_exchange
      ((HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0).map
        (Sigma.ι (fun _ : j ⟶ j => U) (𝟙 j))) (X.map f)).symm
  have hc : Ti.map (Sigma.ι (fun _ : i ⟶ j => U) f) ≫ coend.ι B i =
      (𝟙_ (Complex A) ◁ X.map f) ≫ Tj.map (Sigma.ι (fun _ : j ⟶ j => U) (𝟙 j)) ≫
        coend.ι B j := by
    calc
      _ = Ti.map (Sigma.ι (fun _ : j ⟶ j => U) (𝟙 j)) ≫ (B.map f.op).app i ≫
          coend.ι B i := by
        change _ = Ti.map _ ≫ Ti.map ((freeModuleWeight A j).map f.op) ≫ _
        rw [← Ti.map_comp_assoc, freeModuleWeight_ι_map, Category.comp_id]
      _ = Ti.map (Sigma.ι (fun _ : j ⟶ j => U) (𝟙 j)) ≫ (B.obj (op j)).map f ≫
          coend.ι B j := congrArg (fun h => Ti.map _ ≫ h) (coend.condition (F := B) f)
      _ = _ := by rw [← Category.assoc, he, Category.assoc]
  dsimp only [freeWeightGenerator]
  rw [← Category.assoc, leftUnitor_inv_naturality, Category.assoc]
  exact (congrArg (fun h => (λ_ (X.obj i)).inv ≫ h) hc).symm

/-- 自由表現可能線形重みの coend は、同じ生成元を保って元の値と同型。 -/
def freeWeightEvaluationIso (X : J ⥤ Complex A) (j : J) :
    (linearWeightRealization A X).obj (freeModuleWeight A j) ≅ X.obj j where
  hom := freeWeightEvaluation A X j
  inv := freeWeightGenerator A X j j (𝟙 j)
  hom_inv_id := by
    apply coend.hom_ext (F := (linearWeightBifunctor A X).obj (freeModuleWeight A j))
    intro i
    let Ti := weightTensorAt A X i
    let := weightTensorAt_preservesCoproducts A X i (i ⟶ j)
    apply (cancel_epi (sigmaComparison Ti (fun _ : i ⟶ j => 𝟙_ (ModuleCat.{u} A)))).mp
    apply Sigma.hom_ext
    intro f
    simp only [ι_comp_sigmaComparison_assoc, freeWeightEvaluation,
      coend.ι_desc_assoc]
    change (weightTensorAt A X i).map (Sigma.ι (fun _ : i ⟶ j => 𝟙_ (ModuleCat.{u} A)) f) ≫
      freeWeightLeg A X j i ≫ freeWeightGenerator A X j j (𝟙 j) = _
    rw [map_ι_freeWeightLeg_assoc, freeWeightGenerator_relation]
    change (λ_ (X.obj i)).hom ≫ (λ_ (X.obj i)).inv ≫
      (weightTensorAt A X i).map (Sigma.ι (fun _ : i ⟶ j => 𝟙_ (ModuleCat.{u} A)) f) ≫
      coend.ι ((linearWeightBifunctor A X).obj (freeModuleWeight A j)) i =
      (weightTensorAt A X i).map (Sigma.ι (fun _ : i ⟶ j => 𝟙_ (ModuleCat.{u} A)) f) ≫
      coend.ι ((linearWeightBifunctor A X).obj (freeModuleWeight A j)) i ≫ 𝟙 _
    rw [Iso.hom_inv_id_assoc, Category.comp_id]
  inv_hom_id := by simp

end SerrePositivity.HomologicalAlgebra
