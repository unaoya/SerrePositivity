module
public import SerrePositivity.DifferentialGraded.Endomorphism.ModuleComparison

/-! # 再構成tensorに残るD作用の生成元公式 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)

/-- End(E)作用bimoduleの転置を評価すると、元のEの右D作用になる。 -/
lemma endomorphismModuleAction_transpose (x y : Dᵒᵖ) :
    (endomorphismModuleAction A D E).transposeHom x y ≫
      leftModuleHomπ A (EndomorphismObject E)
        ((endomorphismModuleAction A D E).leftAt x.unop)
        ((endomorphismModuleAction A D E).leftAt y.unop) .point = E.map x y :=
  (endomorphismModuleAction A D E).transposeHom_π x y .point

/-- 再構成tensorの右D作用。次数pの作用は次数rのEnd加群成分を越える符号を持つ。 -/
lemma endomorphismModuleTensor_action_element
    (N : RightModule A (EndomorphismObject E)) (x y : Dᵒᵖ)
    {p r s n : ℤ} (f : GradedHom A x y p)
    (m : (N.obj (op (.point : EndomorphismObject E))).X r) (t : (E.obj x).X s)
    (hn : r + s + p = n) :
    moduleAction A ((endomorphismModuleTensor A D E).obj N) f
      (BalancedTensor.element A (EndomorphismObject E) N
        ((endomorphismModuleAction A D E).leftAt x.unop) .point m t rfl) hn =
    (p * r).negOnePow • BalancedTensor.element A (EndomorphismObject E) N
      ((endomorphismModuleAction A D E).leftAt y.unop) .point m
        (moduleAction A E f t (by omega : s + p = p + s)) (by omega) := by
  change (((BalancedTensor.leftHomMap A (EndomorphismObject E) N
      ((endomorphismModuleAction A D E).leftAt x.unop)
      ((endomorphismModuleAction A D E).leftAt y.unop)).f p
        (((endomorphismModuleAction A D E).transposeHom x y).f p f)).v (r + s) n hn) _ = _
  rw [BalancedTensor.leftHomMap_element]
  have h := congrArg (fun k => k.f p f) (endomorphismModuleAction_transpose A D E x y)
  change (leftModuleHomπ A (EndomorphismObject E)
      ((endomorphismModuleAction A D E).leftAt x.unop)
      ((endomorphismModuleAction A D E).leftAt y.unop) .point).f p
        (((endomorphismModuleAction A D E).transposeHom x y).f p f) = (E.map x y).f p f at h
  rw [h]
  rfl

/-- 入力tensorの総次数を別名にしたD作用の生成元公式。 -/
lemma endomorphismModuleTensor_action_element_of_sum
    (N : RightModule A (EndomorphismObject E)) (x y : Dᵒᵖ)
    {p r s a n : ℤ} (f : GradedHom A x y p)
    (m : (N.obj (op (.point : EndomorphismObject E))).X r) (t : (E.obj x).X s)
    (ha : r + s = a) (hn : a + p = n) :
    moduleAction A ((endomorphismModuleTensor A D E).obj N) (x := x) (y := y) f
      (BalancedTensor.element A (EndomorphismObject E) N
        ((endomorphismModuleAction A D E).leftAt x.unop) .point m t ha) hn =
    (p * r).negOnePow • BalancedTensor.element A (EndomorphismObject E) N
      ((endomorphismModuleAction A D E).leftAt y.unop) .point m
        (moduleAction A E (x := x) (y := y) f t (rfl : s + p = s + p)) (by omega) := by
  change (((BalancedTensor.leftHomMap A (EndomorphismObject E) N
      ((endomorphismModuleAction A D E).leftAt x.unop)
      ((endomorphismModuleAction A D E).leftAt y.unop)).f p
        (((endomorphismModuleAction A D E).transposeHom x y).f p f)).v a n hn) _ = _
  have he := BalancedTensor.leftHomMap_element_of_sum A (EndomorphismObject E) N
    (N := (endomorphismModuleAction A D E).leftAt x.unop)
    (N' := (endomorphismModuleAction A D E).leftAt y.unop)
    (((endomorphismModuleAction A D E).transposeHom x y).f p f) .point m t ha
      (by omega : p + s = s + p) hn
  have h := congrArg (fun k => k.f p f) (endomorphismModuleAction_transpose A D E x y)
  change (leftModuleHomπ A (EndomorphismObject E)
      ((endomorphismModuleAction A D E).leftAt x.unop)
      ((endomorphismModuleAction A D E).leftAt y.unop) .point).f p
        (((endomorphismModuleAction A D E).transposeHom x y).f p f) = (E.map x y).f p f at h
  have hv := congrArg (fun c => c.v s (s + p) rfl t) h
  exact he.trans (congrArg (fun z => (p * r).negOnePow •
    BalancedTensor.element A (EndomorphismObject E) N
      ((endomorphismModuleAction A D E).leftAt y.unop) .point m z (by omega : r + (s + p) = n)) hv)

end SerrePositivity.DifferentialGraded
