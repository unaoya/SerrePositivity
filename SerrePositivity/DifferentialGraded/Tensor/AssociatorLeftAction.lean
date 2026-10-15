module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorElements

/-! # 結合比較の左端のdg作用との整合性 -/
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

lemma associatorLeft_leftAction_element (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (c : C) (e : E) (f f' : F)
    {p k r s i m j n : ℤ} (hi : r + s = i) (hm : k + i = m)
    (hj : k + p = j) (hn : m + p = n) (g : GradedHom A f f' p)
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s) :
    SerrePositivity.DifferentialGraded.leftAction A
      ((compose A B E F (compose A B C E P Q) R).leftAt b) g
      (associatorLeftElement A B C E F P Q R b c e f t q v hi hm) hn =
    associatorLeftElement A B C E F P Q R b c e f'
      (SerrePositivity.DifferentialGraded.leftAction A (R.leftAt e) g t hj) q v hi (by omega) :=
  compose_leftAction_element A B E F (compose A B C E P Q) R b e f f'
    hm hj hn g t (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c q v hi)

lemma associatorRight_leftAction_element (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (c : C) (e : E) (f f' : F)
    {p k r s l m j l' n : ℤ} (hl : k + r = l) (hm : l + s = m)
    (hj : k + p = j) (hl' : l + p = l') (hn : m + p = n) (g : GradedHom A f f' p)
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s) :
    SerrePositivity.DifferentialGraded.leftAction A
      ((compose A B C F P (compose A C E F Q R)).leftAt b) g
      (associatorRightElement A B C E F P Q R b c e f t q v hl hm) hn =
    associatorRightElement A B C E F P Q R b c e f' (l := l')
      (SerrePositivity.DifferentialGraded.leftAction A (R.leftAt e) g t hj) q v
      (by omega) (by omega) := by
  have ho := compose_leftAction_element A B C F P (compose A C E F Q R) b c f f'
    hm hl' hn g (BalancedTensor.element A E (R.rightAt f) (Q.leftAt c) e t q hl) v
  have hi := compose_leftAction_element A C E F Q R c e f f' hl hj hl' g t q
  rw [hi] at ho
  exact ho


end SerrePositivity.DifferentialGraded.BimoduleTensor
