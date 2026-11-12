module

public import SerrePositivity.HomologicalAlgebra.LinearFreeWeight
import all SerrePositivity.HomologicalAlgebra.LinearFreeWeight
import all SerrePositivity.HomologicalAlgebra.LinearWeightRealization

/-!
# 線形 coend の指定生成元

## 概要
重みの単位加群からの射に対応する、元の係数複体から coend への射を構成する。

## 方針
単位子とテンソルの交換則、coend の元の関係式を使う。

## 規約
重みの射と添字の射を同じ生成元で照合する。

## 使われ方
HA 1.2.4。bar の各項を元の射列の余積へ同定する計算。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.HomologicalAlgebra
variable (A : Type u) [CommRing A] {J : Type} [SmallCategory J]

/-- 単位加群からの指定射が与える、同じ coend の生成元。 -/
def linearWeightGenerator (X : J ⥤ Complex A) (W : Jᵒᵖ ⥤ ModuleCat.{u} A)
    (i : J) (e : 𝟙_ (ModuleCat.{u} A) ⟶ W.obj (op i)) :
    X.obj i ⟶ (linearWeightRealization A X).obj W :=
  (λ_ (X.obj i)).inv ≫ (weightTensorAt A X i).map e ≫
    coend.ι ((linearWeightBifunctor A X).obj W) i

/-- 重みの全射は、指定生成元の同じ像を保つ。 -/
@[reassoc]
theorem linearWeightGenerator_map (X : J ⥤ Complex A)
    {W V : Jᵒᵖ ⥤ ModuleCat.{u} A} (α : W ⟶ V) (i : J)
    (e : 𝟙_ (ModuleCat.{u} A) ⟶ W.obj (op i)) :
    linearWeightGenerator A X W i e ≫ (linearWeightRealization A X).map α =
      linearWeightGenerator A X V i (e ≫ α.app (op i)) := by
  dsimp only [linearWeightGenerator, linearWeightRealization]
  simp only [Functor.comp_map, coendFunctor_map, Category.assoc, coend.ι_map]
  change _ = (λ_ (X.obj i)).inv ≫
    (weightTensorAt A X i).map (e ≫ α.app (op i)) ≫ _
  rw [(weightTensorAt A X i).map_comp, Category.assoc]
  rfl

/-- 添字の射に関する coend の関係式を、同じ生成元で書いたもの。 -/
@[reassoc]
theorem linearWeightGenerator_relation (X : J ⥤ Complex A)
    (W : Jᵒᵖ ⥤ ModuleCat.{u} A) {i k : J} (f : i ⟶ k)
    (e : 𝟙_ (ModuleCat.{u} A) ⟶ W.obj (op k)) :
    X.map f ≫ linearWeightGenerator A X W k e =
      linearWeightGenerator A X W i (e ≫ W.map f.op) := by
  let B := (linearWeightBifunctor A X).obj W
  let Ti := weightTensorAt A X i
  have he : Ti.map e ≫ (B.obj (op k)).map f =
      (𝟙_ (Complex A) ◁ X.map f) ≫ (weightTensorAt A X k).map e := by
    exact (whisker_exchange
      ((HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0).map e) (X.map f)).symm
  dsimp only [linearWeightGenerator]
  rw [← Category.assoc, leftUnitor_inv_naturality, Category.assoc]
  change _ = (λ_ (X.obj i)).inv ≫ Ti.map (e ≫ W.map f.op) ≫ coend.ι B i
  rw [Ti.map_comp, Category.assoc]
  change _ = (λ_ (X.obj i)).inv ≫ Ti.map e ≫ (B.map f.op).app i ≫ coend.ι B i
  rw [coend.condition, ← Category.assoc (Ti.map e), he, Category.assoc]

end SerrePositivity.HomologicalAlgebra
