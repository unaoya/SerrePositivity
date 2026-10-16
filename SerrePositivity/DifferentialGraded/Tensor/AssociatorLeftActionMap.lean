module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorCochainAction

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

/-- 左作用の生成元公式を任意の値写像の後で使う。 -/
lemma associatorLeftCochain_element_map (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (c : C) (e : E) (f f' : F)
    {p k r s i j m n : ℤ} (hi : r + s = i) (hm : k + i = m)
    (hj : k + p = j) (hn : m + p = n) (g : GradedHom A f f' p)
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s)
    {Z : Type u}
    (a : ((compose A B E F (compose A B C E P Q) R).value b f').X n → Z) :
    a ((associatorLeftCochain A B C E F P Q R b f f' p g).v m n hn
      (associatorLeftElement A B C E F P Q R b c e f t q v hi hm)) =
    a (associatorLeftElement A B C E F P Q R b c e f'
      (SerrePositivity.DifferentialGraded.leftAction A (R.leftAt e) g t hj)
      q v hi (by omega)) :=
  congrArg a (associatorLeftCochain_element A B C E F P Q R b c e f f'
    (p := p) (k := k) (r := r) (s := s) (i := i) (j := j) (m := m) (n := n)
    hi hm hj hn g t q v)

end SerrePositivity.DifferentialGraded.BimoduleTensor
