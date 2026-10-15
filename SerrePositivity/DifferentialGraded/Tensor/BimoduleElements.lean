module
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule
public import SerrePositivity.DifferentialGraded.Tensor.HomElements

/-! # bimodule合成の左作用の斉次生成元公式 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

/-- 合成の左作用は先頭のtensor因子へ作用し、余分な符号を生じない。 -/
lemma compose_leftAction_element (P : Bimodule A B C) (Q : Bimodule A C E)
    (b : B) (c : C) (e e' : E) {p k r i j n : ℤ}
    (ha : k + r = i) (hj : k + p = j) (hn : i + p = n)
    (g : GradedHom A e e' p) (q : (Q.value c e).X k) (v : (P.value b c).X r) :
    SerrePositivity.DifferentialGraded.leftAction A ((compose A B C E P Q).leftAt b) g
      (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c q v ha) hn =
    BalancedTensor.element A C (Q.rightAt e') (P.leftAt b) c
      (SerrePositivity.DifferentialGraded.leftAction A (Q.leftAt c) g q hj) v (by omega) := by
  have h := compose_leftMap_π A B C E P Q e e' b
  change ((compose A B C E P Q).leftAt b).map e e' =
    Q.toFunctor.map e e' ≫
      BalancedTensor.rightHomMap A C (Q.rightAt e) (Q.rightAt e') (P.leftAt b) at h
  have hc := congrArg (fun z => z.f p g) h
  have he := BalancedTensor.rightHomMap_element_of_sum A C (P.leftAt b) (l := j)
    ((Q.toFunctor.map e e').f p g) c q v ha (by omega) hn
  exact (congrArg (fun z => z.v i n hn
    (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c q v ha)) hc).trans he

end SerrePositivity.DifferentialGraded.BimoduleTensor
