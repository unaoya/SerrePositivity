module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorLeftMaps
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorRightMaps

/-! # 左端作用cochainの三重生成元上の計算

実際のHom写像の評価と既存の作用計算を、結合同型との比較から独立に検証する。
-/
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

/-- 左括弧のF作用cochainは三重生成元のR成分に作用する。 -/
lemma associatorLeftCochain_element (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (c : C) (e : E) (f f' : F)
    {p k r s i m j n : ℤ} (hi : r + s = i) (hm : k + i = m)
    (hj : k + p = j) (hn : m + p = n) (g : GradedHom A f f' p)
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s) :
    (associatorLeftCochain A B C E F P Q R b f f' p g).v m n hn
      (associatorLeftElement A B C E F P Q R b c e f t q v hi hm) =
    associatorLeftElement A B C E F P Q R b c e f'
      (SerrePositivity.DifferentialGraded.leftAction A (R.leftAt e) g t hj)
      q v hi (by omega) :=
  (associatorLeftCochain_apply A B C E F P Q R b f f' g _ hn).trans
    (associatorLeft_leftAction_element A B C E F P Q R b c e f f' hi hm hj hn g t q v)

/-- 右括弧のF作用cochainも三重生成元のR成分に作用する。 -/
lemma associatorRightCochain_element (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (c : C) (e : E) (f f' : F)
    {p k r s l m j l' n : ℤ} (hl : k + r = l) (hm : l + s = m)
    (hj : k + p = j) (hl' : l + p = l') (hn : m + p = n) (g : GradedHom A f f' p)
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s) :
    (associatorRightCochain A B C E F P Q R b f f' p g).v m n hn
      (associatorRightElement A B C E F P Q R b c e f t q v hl hm) =
    associatorRightElement A B C E F P Q R b c e f' (l := l')
      (SerrePositivity.DifferentialGraded.leftAction A (R.leftAt e) g t hj)
      q v (by omega) (by omega) :=
  (associatorRightCochain_apply A B C E F P Q R b f f' g _ hn).trans
    (associatorRight_leftAction_element A B C E F P Q R b c e f f' hl hm hj hl' hn g t q v)

/-- 左括弧の右B作用cochainはR/Qの次数の和とのKoszul符号を持つ。 -/
lemma associatorLeftBCochain_element (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b b' : Bᵒᵖ) (c : C) (e : E) (f : F)
    {p k r s i j i' m n : ℤ} (hi : r + s = i) (hm : k + i = m)
    (hj : s + p = j) (hi' : i + p = i') (hn : m + p = n) (g : GradedHom A b b' p)
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b.unop c).X s) :
    (associatorLeftBCochain A B C E F P Q R b b' f p g).v m n hn
      (associatorLeftElement A B C E F P Q R b.unop c e f t q v hi hm) =
    (p * (k + r)).negOnePow •
      associatorLeftElement A B C E F P Q R b'.unop c e f (i := i') (n := n) t q
        (moduleAction A (P.rightAt c) g v hj) (by omega) (by omega) :=
  (associatorLeftBCochain_apply A B C E F P Q R b b' f g _ hn).trans
    (associatorLeft_rightAction_element A B C E F P Q R b b' c e f hi hm hj hi' hn g t q v)

/-- 右括弧の右B作用cochainは内側coend全体の次数とのKoszul符号を持つ。 -/
lemma associatorRightBCochain_element (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b b' : Bᵒᵖ) (c : C) (e : E) (f : F)
    {p k r s l j m n : ℤ} (hl : k + r = l) (hm : l + s = m)
    (hj : s + p = j) (hn : m + p = n) (g : GradedHom A b b' p)
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b.unop c).X s) :
    (associatorRightBCochain A B C E F P Q R b b' f p g).v m n hn
      (associatorRightElement A B C E F P Q R b.unop c e f t q v hl hm) =
    (p * l).negOnePow •
      associatorRightElement A B C E F P Q R b'.unop c e f (l := l) (n := n) t q
        (moduleAction A (P.rightAt c) g v hj) hl (by omega) :=
  (associatorRightBCochain_apply A B C E F P Q R b b' f g _ hn).trans
    (associatorRight_rightAction_element A B C E F P Q R b b' c e f hl hm hj hn g t q v)

end SerrePositivity.DifferentialGraded.BimoduleTensor
