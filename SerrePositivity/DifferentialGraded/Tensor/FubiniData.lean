module
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule
public import SerrePositivity.DifferentialGraded.Tensor.ParameterEvaluation
public import SerrePositivity.DifferentialGraded.Tensor.HomElements

/-! # Fubini比較の二つの反復tensorと三重生成元 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.BalancedTensor.Fubini
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (C : Type v) (E : Type w)
  [DGCategory A C] [DGCategory A E] [Small.{u} C] [Small.{u} E]

/-- Q(c,e)⊗_C N(c)を値とする左E加群。 -/
def leftModule (Q : Bimodule A C E) (N : LeftModule A C) : LeftModule A E :=
  Q.toFunctor.comp (rightTensorDG A C N)

/-- R(e)⊗_E Q(c,e)を値とする右C加群。 -/
def rightModule (Q : Bimodule A C E) (R : RightModule A E) : RightModule A C :=
  Q.transposeDG.comp (leftTensorDG A E R)

/-- R⊗_E(Q⊗_C N)。 -/
def leftObj (Q : Bimodule A C E) (R : RightModule A E) (N : LeftModule A C) : Complex A :=
  obj A E R (leftModule A C E Q N)

/-- (R⊗_E Q)⊗_C N。 -/
def rightObj (Q : Bimodule A C E) (R : RightModule A E) (N : LeftModule A C) : Complex A :=
  obj A C (rightModule A C E Q R) N

/-- 三重tensorから左側の反復coendへの包含。 -/
def leftι (Q : Bimodule A C E) (R : RightModule A E) (N : LeftModule A C) (c : C) (e : E) :
    R.obj (op e) ⊗ (Q.value c e ⊗ N.obj c) ⟶ leftObj A C E Q R N :=
  (R.obj (op e) ◁ ι A C (Q.rightAt e) N c) ≫ ι A E R (leftModule A C E Q N) e

/-- 同じ順序の三重tensorから右側の反復coendへの包含。 -/
def rightι (Q : Bimodule A C E) (R : RightModule A E) (N : LeftModule A C) (c : C) (e : E) :
    R.obj (op e) ⊗ (Q.value c e ⊗ N.obj c) ⟶ rightObj A C E Q R N :=
  (α_ (R.obj (op e)) (Q.value c e) (N.obj c)).inv ≫
    (ι A E R (Q.leftAt c) e ▷ N.obj c) ≫ ι A C (rightModule A C E Q R) N c

/-- 左反復coendからの射は三重生成元で判定できる。 -/
lemma left_hom_ext (Q : Bimodule A C E) (R : RightModule A E) (N : LeftModule A C)
    {T : Complex A} {f g : leftObj A C E Q R N ⟶ T}
    (h : ∀ c e, leftι A C E Q R N c e ≫ f = leftι A C E Q R N c e ≫ g) : f = g := by
  apply hom_ext A E R (leftModule A C E Q N)
  intro e
  apply param_hom_ext A C (Q.rightAt e) N
  intro c
  exact h c e

/-- 右反復coendからの射も同じ順序の三重生成元で判定できる。 -/
lemma right_hom_ext (Q : Bimodule A C E) (R : RightModule A E) (N : LeftModule A C)
    {T : Complex A} {f g : rightObj A C E Q R N ⟶ T}
    (h : ∀ c e, rightι A C E Q R N c e ≫ f = rightι A C E Q R N c e ≫ g) : f = g := by
  apply hom_ext A C (rightModule A C E Q R) N
  intro c
  apply rightParam_hom_ext A E R (Q.leftAt c)
  intro e
  apply (cancel_epi (α_ (R.obj (op e)) (Q.value c e) (N.obj c)).inv).1
  simpa only [rightι, Category.assoc] using h c e

omit [Small.{u} E] in
/-- 左E作用を内側のC-coendの生成元で計算する。 -/
lemma leftModule_action_element (Q : Bimodule A C E) (N : LeftModule A C) (e e' : E) (c : C)
    {p r s a j n : ℤ} (ha : r + s = a) (hj : r + p = j) (hn : a + p = n)
    (f : GradedHom A e e' p) (q : (Q.value c e).X r) (v : (N.obj c).X s) :
    SerrePositivity.DifferentialGraded.leftAction A (leftModule A C E Q N) f
      (element A C (Q.rightAt e) N c q v ha) hn =
    element A C (Q.rightAt e') N c
      (SerrePositivity.DifferentialGraded.leftAction A (Q.leftAt c) f q hj) v (by omega) := by
  change (((rightHomMap A C (Q.rightAt e) (Q.rightAt e') N).f p
    ((Q.toFunctor.map e e').f p f)).v a n hn) (element A C (Q.rightAt e) N c q v ha) = _
  rw [rightHomMap_element_of_sum A C N (l := j) _ c q v ha (by omega) hn]
  rfl

end SerrePositivity.DifferentialGraded.BalancedTensor.Fubini
