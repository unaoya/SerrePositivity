module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorCochainAction
public import SerrePositivity.DifferentialGraded.Bimodule.ActionElement

/-! # 左作用を適用した三重生成元の結合比較 -/
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

/-- 左作用後の生成元を結合同型で送る。 -/
lemma associatorValueIso_hom_actionElement_of_degree (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (c : C) (e : E) (f f' : F) {p k r s i j l n : ℤ}
    (hi : r + s = i) (hj : k + p = j) (hl : j + r = l) (hn : j + i = n) (g : GradedHom A f f' p)
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s) :
    (associatorValueIso A B C E F P Q R b f').hom.f n
      (associatorLeftElement A B C E F P Q R b c e f' (n := n)
        (Bimodule.leftActionElement A R g e t hj)
        q v hi hn) =
    associatorRightElement A B C E F P Q R b c e f' (l := l) (n := n)
      (Bimodule.leftActionElement A R g e t hj)
      q v hl (by omega) :=
  associatorValueIso_hom_element A B C E F P Q R b c e f'
    (k := j) (r := r) (s := s) (i := i) (l := l) (n := n)
    (Bimodule.leftActionElement A R (n := j) g e t hj)
    q v hi hl hn

/-- 左作用後の生成元を結合同型で送る。 -/
lemma associatorValueIso_hom_leftActed_of_degree (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (c : C) (e : E) (f f' : F) {p k r s i j l n : ℤ}
    (hi : r + s = i) (hj : k + p = j) (hl : j + r = l) (hn : j + i = n) (g : GradedHom A f f' p)
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s) :
    (associatorValueIso A B C E F P Q R b f').hom.f n
      (associatorLeftElement A B C E F P Q R b c e f' (n := n)
        (SerrePositivity.DifferentialGraded.leftAction A (R.leftAt e) g t hj)
        q v hi hn) =
    associatorRightElement A B C E F P Q R b c e f' (l := l) (n := n)
      (SerrePositivity.DifferentialGraded.leftAction A (R.leftAt e) g t hj)
      q v hl (by omega) :=
  associatorValueIso_hom_element A B C E F P Q R b c e f'
    (k := j) (r := r) (s := s) (i := i) (l := l) (n := n)
    (SerrePositivity.DifferentialGraded.leftAction A (R.leftAt e) (n := j) g t hj)
    q v hi hl hn

end SerrePositivity.DifferentialGraded.BimoduleTensor
