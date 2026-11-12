module

public import SerrePositivity.HomologicalAlgebra.LinearCoYoneda
import all SerrePositivity.HomologicalAlgebra.LinearCoYoneda
import all SerrePositivity.HomologicalAlgebra.LinearFreeWeight
import all SerrePositivity.HomologicalAlgebra.LinearWeightRealization
import all SerrePositivity.HomologicalAlgebra.FreePresheafFunctor

/-!
# 自由線形重みの評価の全自然性

## 概要
coend の自由重みの評価を、表現対象の全射に関する自然同型にまとめる。

## 方針
各 coend 包含と余積の生成元に制限し、元の図式の合成の法則を使う。

## 規約
同型の成分は元の評価射・恒等射の生成元そのもの。

## 使われ方
HA 1.2.4。標準単体重みの全単体作用素を保った計算複体への比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.HomologicalAlgebra
variable (A : Type u) [CommRing A] {J : Type} [SmallCategory J]

/-- 表現対象を動かすときの、元の余積の同じ生成元の公式。 -/
@[reassoc]
theorem freeModuleWeight_ι_targetMap {j k : J} (g : j ⟶ k) (i : J) (f : i ⟶ j) :
    Sigma.ι (fun _ : i ⟶ j => 𝟙_ (ModuleCat.{u} A)) f ≫
        ((freePresheafFunctor J (𝟙_ (ModuleCat.{u} A))).map g).app (op i) =
      Sigma.ι (fun _ : i ⟶ k => 𝟙_ (ModuleCat.{u} A)) (f ≫ g) := by
  simp [freePresheafFunctor, copowerFunctor]

/-- 評価は表現対象のすべての射と、元の同じ図式の射で両立する。 -/
theorem freeWeightEvaluation_naturality (X : J ⥤ Complex A) {j k : J} (g : j ⟶ k) :
    (linearWeightRealization A X).map
        ((freePresheafFunctor J (𝟙_ (ModuleCat.{u} A))).map g) ≫ freeWeightEvaluation A X k =
      freeWeightEvaluation A X j ≫ X.map g := by
  let B := (linearWeightBifunctor A X).obj (freeModuleWeight A j)
  apply coend.hom_ext (F := B)
  intro i
  let Ti := weightTensorAt A X i
  let := weightTensorAt_preservesCoproducts A X i (i ⟶ j)
  apply (cancel_epi (sigmaComparison Ti (fun _ : i ⟶ j => 𝟙_ (ModuleCat.{u} A)))).mp
  apply Sigma.hom_ext
  intro f
  simp only [ι_comp_sigmaComparison_assoc, linearWeightRealization,
    Functor.comp_map, coendFunctor_map, coend.ι_map_assoc, freeWeightEvaluation,
    coend.ι_desc, coend.ι_desc_assoc]
  change Ti.map (Sigma.ι (fun _ : i ⟶ j => 𝟙_ (ModuleCat.{u} A)) f) ≫
    Ti.map (((freePresheafFunctor J (𝟙_ (ModuleCat.{u} A))).map g).app (op i)) ≫
      freeWeightLeg A X k i =
    Ti.map (Sigma.ι (fun _ : i ⟶ j => 𝟙_ (ModuleCat.{u} A)) f) ≫ freeWeightLeg A X j i ≫ X.map g
  rw [← Ti.map_comp_assoc, freeModuleWeight_ι_targetMap, map_ι_freeWeightLeg,
    map_ι_freeWeightLeg_assoc, X.map_comp]

/-- 全表現対象・全射での同じ線形 co-Yoneda 同型。 -/
def freeWeightEvaluationNatIso (X : J ⥤ Complex A) :
    freePresheafFunctor J (𝟙_ (ModuleCat.{u} A)) ⋙ linearWeightRealization A X ≅ X :=
  NatIso.ofComponents (freeWeightEvaluationIso A X) (fun g => freeWeightEvaluation_naturality A X g)

end SerrePositivity.HomologicalAlgebra
