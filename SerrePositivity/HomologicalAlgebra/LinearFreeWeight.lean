module

public import SerrePositivity.HomologicalAlgebra.LinearWeightRealization
public import SerrePositivity.HomologicalAlgebra.FreePresheafFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all SerrePositivity.HomologicalAlgebra.LinearWeightRealization
import all SerrePositivity.HomologicalAlgebra.FreePresheafFunctor

/-!
# 自由線形重みの coend の元の生成元

## 概要
自由表現可能加群重みをテンソルする各因子から、元の図式の指定した値への射を作る。

## 方針
single とテンソルの余積保存で各生成元へ分け、単位子と元の図式の同じ射を合成する。

## 規約
同じ単位加群の余積、同じテンソル因子、同じ図式の射を使う。

## 使われ方
HA 1.2.4、Weibel §2.2。線形重みの coend と単体次数で添字づけた複体の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.HomologicalAlgebra
variable (A : Type u) [CommRing A] {J : Type} [SmallCategory J]

/-- 元の図式の一つの値と、次数零の加群をテンソルする同じ関手。 -/
def weightTensorAt (X : J ⥤ Complex A) (i : J) : ModuleCat.{u} A ⥤ Complex A :=
  HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0 ⋙
    (tensoringRight (Complex A)).obj (X.obj i)

/-- 必要な小さい余積は、single と右側のテンソルを通して保たれる。 -/
theorem weightTensorAt_preservesCoproducts (X : J ⥤ Complex A) (i : J) (I : Type) :
    PreservesColimitsOfShape (Discrete I) (weightTensorAt A X i) := by
  dsimp [weightTensorAt]
  infer_instance

/-- 自由重みの各生成元を、元の図式の同じ射へ送る射。 -/
def freeWeightLeg (X : J ⥤ Complex A) (j i : J) :
    (weightTensorAt A X i).obj (∐ (fun _ : i ⟶ j => 𝟙_ (ModuleCat.{u} A))) ⟶ X.obj j := by
  let T := weightTensorAt A X i
  have : PreservesColimit (Discrete.functor (fun _ : i ⟶ j => 𝟙_ (ModuleCat.{u} A))) T := by
    dsimp [T, weightTensorAt]
    infer_instance
  exact inv (sigmaComparison T (fun _ : i ⟶ j => 𝟙_ (ModuleCat.{u} A))) ≫
    Sigma.desc (fun f => (λ_ (X.obj i)).hom ≫ X.map f)

/-- 元の各生成元に制限すると、単位子の後の同じ図式の射となる。 -/
@[reassoc]
theorem map_ι_freeWeightLeg (X : J ⥤ Complex A) (j i : J) (f : i ⟶ j) :
    (weightTensorAt A X i).map (Sigma.ι (fun _ : i ⟶ j => 𝟙_ (ModuleCat.{u} A)) f) ≫
      freeWeightLeg A X j i = (λ_ (X.obj i)).hom ≫ X.map f := by
  let := weightTensorAt_preservesCoproducts A X i (i ⟶ j)
  dsimp only [freeWeightLeg]
  simp only [map_ι_comp_inv_sigmaComparison_assoc, Sigma.ι_comp_desc]

/-- 単位加群を係数とする、元の自由表現可能な線形重み。 -/
def freeModuleWeight (j : J) : Jᵒᵖ ⥤ ModuleCat.{u} A :=
  (freePresheafFunctor J (𝟙_ (ModuleCat.{u} A))).obj j

/-- 自由重みの各生成元に対する、元の図式の添字の前合成の公式。 -/
@[reassoc]
theorem freeModuleWeight_ι_map (j : J) {i k : J} (g : i ⟶ k) (f : k ⟶ j) :
    Sigma.ι (fun _ : k ⟶ j => 𝟙_ (ModuleCat.{u} A)) f ≫ (freeModuleWeight A j).map g.op =
      Sigma.ι (fun _ : i ⟶ j => 𝟙_ (ModuleCat.{u} A)) (g ≫ f) := by
  simp [freeModuleWeight, freePresheafFunctor, copowerFunctor]

/-- 元の生成元上の射は、同じ coend の余関手的な二つの射に両立する。 -/
theorem freeWeightLeg_condition (X : J ⥤ Complex A) (j : J) {i k : J} (g : i ⟶ k) :
    (((linearWeightBifunctor A X).obj (freeModuleWeight A j)).map g.op).app i ≫
        freeWeightLeg A X j i =
      (((linearWeightBifunctor A X).obj (freeModuleWeight A j)).obj (Opposite.op k)).map g ≫
        freeWeightLeg A X j k := by
  let Ti := weightTensorAt A X i
  let Tk := weightTensorAt A X k
  let U := 𝟙_ (ModuleCat.{u} A)
  let := weightTensorAt_preservesCoproducts A X i (k ⟶ j)
  apply (cancel_epi (sigmaComparison Ti (fun _ : k ⟶ j => U))).mp
  apply Sigma.hom_ext
  intro f
  simp only [ι_comp_sigmaComparison_assoc]
  have he : Ti.map (Sigma.ι (fun _ : k ⟶ j => U) f) ≫
      (((linearWeightBifunctor A X).obj (freeModuleWeight A j)).obj (Opposite.op k)).map g =
      (𝟙_ (Complex A) ◁ X.map g) ≫ Tk.map (Sigma.ι (fun _ : k ⟶ j => U) f) := by
    exact (whisker_exchange
      ((HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0).map
        (Sigma.ι (fun _ : k ⟶ j => U) f)) (X.map g)).symm
  change Ti.map (Sigma.ι (fun _ : k ⟶ j => U) f) ≫
      Ti.map ((freeModuleWeight A j).map g.op) ≫ freeWeightLeg A X j i = _
  rw [← Ti.map_comp_assoc, freeModuleWeight_ι_map, map_ι_freeWeightLeg]
  rw [← Category.assoc, he, Category.assoc, map_ι_freeWeightLeg]
  rw [X.map_comp, ← leftUnitor_naturality_assoc]

end SerrePositivity.HomologicalAlgebra
