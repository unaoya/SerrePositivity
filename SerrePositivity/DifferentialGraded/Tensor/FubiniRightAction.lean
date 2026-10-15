module
public import SerrePositivity.DifferentialGraded.Tensor.FubiniData

/-! # 右反復tensorの内側に誘導される右作用の符号 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.BalancedTensor.Fubini
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (C : Type v) (E : Type w)
  [DGCategory A C] [DGCategory A E] [Small.{u} C] [Small.{u} E]

/-- 右C作用はRの次数とのKoszul符号を伴いQへ作用する。 -/
lemma rightModule_action_element (Q : Bimodule A C E) (R : RightModule A E)
    (c c' : Cᵒᵖ) (e : E) {p k r a j n : ℤ}
    (ha : k + r = a) (hj : r + p = j) (hn : a + p = n)
    (f : GradedHom A c c' p) (t : (R.obj (op e)).X k) (q : (Q.value c.unop e).X r) :
    moduleAction A (rightModule A C E Q R) f
      (element A E R (Q.leftAt c.unop) e t q ha) hn =
    (p * k).negOnePow • element A E R (Q.leftAt c'.unop) e t
      (moduleAction A (Q.rightAt e) f q hj) (by omega) := by
  change (((leftHomMap A E R (Q.leftAt c.unop) (Q.leftAt c'.unop)).f p
    ((Q.transposeHom c c').f p f)).v a n hn)
      (element A E R (Q.leftAt c.unop) e t q ha) = _
  have he := leftHomMap_element_of_sum A E R (l := j)
    ((Q.transposeHom c c').f p f) e t q ha (by omega) hn
  have h := congrArg (fun z => z.f p f) (Q.transposeHom_π c c' e)
  change (leftModuleHomπ A E (Q.leftAt c.unop) (Q.leftAt c'.unop) e).f p
      ((Q.transposeHom c c').f p f) = ((Q.rightAt e).map c c').f p f at h
  rw [h] at he
  exact he

end SerrePositivity.DifferentialGraded.BalancedTensor.Fubini
