module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorComponent
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorLeftActionMap

/-! # 結合比較と左作用の二段の生成元輸送 -/
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

/-- 左作用後に結合同型を適用した生成元の評価。 -/
lemma associatorLeftComponent_transport (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (c : C) (e : E) (f f' : F) {p k r s i j l m n : ℤ}
    (hi : r + s = i) (hm : k + i = m) (hj : k + p = j)
    (hl : j + r = l) (hn : m + p = n) (g : GradedHom A f f' p)
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s) :
    associatorValueComponent A B C E F P Q R b f' n
      ((associatorLeftCochain A B C E F P Q R b f f' p g).v m n hn
        (associatorLeftElement A B C E F P Q R b c e f (n := m) t q v hi hm)) =
    associatorRightElement A B C E F P Q R b c e f' (l := l) (n := n)
      (SerrePositivity.DifferentialGraded.leftAction A (R.leftAt e) g t hj)
      q v hl (by omega) := by
  exact (associatorLeftCochain_element_map A B C E F P Q R b c e f f'
    hi hm hj hn g t q v
    (fun z => associatorValueComponent A B C E F P Q R b f' n z)).trans
    (associatorValueComponent_element A B C E F P Q R b c e f'
      (k := j) (r := r) (s := s) (i := i) (l := l) (n := n)
      (SerrePositivity.DifferentialGraded.leftAction A (R.leftAt e) (n := j) g t hj)
      q v hi hl (by omega))

end SerrePositivity.DifferentialGraded.BimoduleTensor
