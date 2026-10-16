module
public import SerrePositivity.DifferentialGraded.Bimodule.LeftEvaluation
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule
public import SerrePositivity.DifferentialGraded.Tensor.Functor

/-! # bimodule射の相対tensorへの作用を各値で構成する -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

/-- bimodule射を左右から作用させた、相対tensorの各値のchain map。 -/
def composeValueMap {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
    (f : P ⟶ P') (g : Q ⟶ Q') (b : B) (e : E) :
    (compose A B C E (BimoduleCategory.underlying A B C P)
      (BimoduleCategory.underlying A C E Q)).value b e ⟶
    (compose A B C E (BimoduleCategory.underlying A B C P')
      (BimoduleCategory.underlying A C E Q')).value b e :=
  BalancedTensor.map A C
    (M := (BimoduleCategory.evaluation A C E e).obj Q)
    (M' := (BimoduleCategory.evaluation A C E e).obj Q')
    (N := (BimoduleCategory.leftEvaluation A B C b).obj P)
    (N' := (BimoduleCategory.leftEvaluation A B C b).obj P')
    ((BimoduleCategory.evaluation A C E e).map g)
    ((BimoduleCategory.leftEvaluation A B C b).map f)

@[reassoc (attr := simp)]
lemma ι_composeValueMap {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
    (f : P ⟶ P') (g : Q ⟶ Q') (b : B) (c : C) (e : E) :
    BalancedTensor.ι A C ((BimoduleCategory.underlying A C E Q).rightAt e)
      ((BimoduleCategory.underlying A B C P).leftAt b) c ≫ composeValueMap A B C E f g b e =
    ((BimoduleCategory.valueEvaluation A C E c e).map g ⊗ₘ
      (BimoduleCategory.valueEvaluation A B C b c).map f) ≫
    BalancedTensor.ι A C ((BimoduleCategory.underlying A C E Q').rightAt e)
      ((BimoduleCategory.underlying A B C P').leftAt b) c := by
  have hh := BalancedTensor.ι_map A C
    (M := (BimoduleCategory.evaluation A C E e).obj Q)
    (M' := (BimoduleCategory.evaluation A C E e).obj Q')
    (N := (BimoduleCategory.leftEvaluation A B C b).obj P)
    (N' := (BimoduleCategory.leftEvaluation A B C b).obj P')
    ((BimoduleCategory.evaluation A C E e).map g)
    ((BimoduleCategory.leftEvaluation A B C b).map f) c
  have he := BimoduleCategory.leftEvaluation_map_eval A B C f b c
  exact hh.trans (congrArg (fun k : (BimoduleCategory.underlying A B C P).value b c ⟶
      (BimoduleCategory.underlying A B C P').value b c =>
    ((BimoduleCategory.valueEvaluation A C E c e).map g ⊗ₘ k) ≫
      BalancedTensor.ι A C ((BimoduleCategory.underlying A C E Q').rightAt e)
        ((BimoduleCategory.underlying A B C P').leftAt b) c) he)

lemma composeValueMap_id (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E)
    (b : B) (e : E) :
    composeValueMap A B C E (𝟙 P) (𝟙 Q) b e = 𝟙 _ := by
  unfold composeValueMap
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  exact BalancedTensor.map_id A C _ _

lemma composeValueMap_comp {P P' P'' : BimoduleCategory A B C}
    {Q Q' Q'' : BimoduleCategory A C E} (f : P ⟶ P') (f' : P' ⟶ P'')
    (g : Q ⟶ Q') (g' : Q' ⟶ Q'') (b : B) (e : E) :
    composeValueMap A B C E (f ≫ f') (g ≫ g') b e =
      composeValueMap A B C E f g b e ≫ composeValueMap A B C E f' g' b e := by
  unfold composeValueMap
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  exact BalancedTensor.map_comp A C _ _ _ _

/-- 固定した両端の値における、実際の閉零bimodule圏上のtensor双関手。 -/
def valueFunctor (b : B) (e : E) :
    BimoduleCategory A B C × BimoduleCategory A C E ⥤ Complex A where
  obj PQ := (compose A B C E (BimoduleCategory.underlying A B C PQ.1)
    (BimoduleCategory.underlying A C E PQ.2)).value b e
  map fg := composeValueMap A B C E fg.1 fg.2 b e
  map_id PQ := composeValueMap_id A B C E PQ.1 PQ.2 b e
  map_comp fg gh := composeValueMap_comp A B C E fg.1 gh.1 fg.2 gh.2 b e

end SerrePositivity.DifferentialGraded.BimoduleTensor
