module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorElements
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleRightElements

/-! # 両括弧付けの右B作用と三重生成元の符号 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

/-- 左括弧の右B作用はR/Qの次数の和とのKoszul符号を伴う。 -/
lemma associatorLeft_rightAction_element (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b b' : Bᵒᵖ) (c : C) (e : E) (f : F)
    {p k r s i j i' m n : ℤ} (hi : r + s = i) (hm : k + i = m)
    (hj : s + p = j) (hi' : i + p = i') (hn : m + p = n) (g : GradedHom A b b' p)
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b.unop c).X s) :
    moduleAction A ((compose A B E F (compose A B C E P Q) R).rightAt f) g
      (associatorLeftElement A B C E F P Q R b.unop c e f t q v hi hm) hn =
    (p * (k + r)).negOnePow •
      associatorLeftElement A B C E F P Q R b'.unop c e f (i := i') (n := n) t q
        (moduleAction A (P.rightAt c) g v hj) (by omega) (by omega) := by
  have ho := compose_rightAction_element A B E F (compose A B C E P Q) R b b' e f
    hm hi' hn g t (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b.unop) c q v hi)
  have hi₀ := compose_rightAction_element A B C E P Q b b' c e hi hj hi' g q v
  rw [hi₀, BalancedTensor.element_units_smul_right, smul_smul, ← Int.negOnePow_add] at ho
  have hs : p * k + p * r = p * (k + r) := by ring
  rw [hs] at ho
  exact ho

/-- 右括弧の右B作用では内側coend全体の次数が同じ符号を与える。 -/
lemma associatorRight_rightAction_element (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b b' : Bᵒᵖ) (c : C) (e : E) (f : F)
    {p k r s l j m n : ℤ} (hl : k + r = l) (hm : l + s = m)
    (hj : s + p = j) (hn : m + p = n) (g : GradedHom A b b' p)
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b.unop c).X s) :
    moduleAction A ((compose A B C F P (compose A C E F Q R)).rightAt f) g
      (associatorRightElement A B C E F P Q R b.unop c e f t q v hl hm) hn =
    (p * l).negOnePow •
      associatorRightElement A B C E F P Q R b'.unop c e f (l := l) (n := n) t q
        (moduleAction A (P.rightAt c) g v hj) hl (by omega) :=
  compose_rightAction_element A B C F P (compose A C E F Q R) b b' c f hm hj hn g
    (BalancedTensor.element A E (R.rightAt f) (Q.leftAt c) e t q hl) v

end SerrePositivity.DifferentialGraded.BimoduleTensor
