module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorActionDegree

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

/-- 結合同型の成分を、両括弧の値を型に固定した関数として読む。 -/
@[irreducible]
def associatorValueComponent (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (f : F) (n : ℤ) :
    ((compose A B E F (compose A B C E P Q) R).value b f).X n →
      ((compose A B C F P (compose A C E F Q R)).value b f).X n :=
  fun z => (associatorValueIso A B C E F P Q R b f).hom.f n z

lemma associatorValueComponent_eq (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (f : F) (n : ℤ)
    (z : ((compose A B E F (compose A B C E P Q) R).value b f).X n) :
    associatorValueComponent A B C E F P Q R b f n z =
      (associatorValueIso A B C E F P Q R b f).hom.f n z := by
  unfold associatorValueComponent
  rfl

lemma associatorValueComponent_element (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (c : C) (e : E) (f : F) {k r s i l n : ℤ}
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hi : r + s = i) (hl : k + r = l) (hn : k + i = n) :
    associatorValueComponent A B C E F P Q R b f n
      (associatorLeftElement A B C E F P Q R b c e f t q v hi hn) =
    associatorRightElement A B C E F P Q R b c e f t q v hl (by omega) :=
  (associatorValueComponent_eq A B C E F P Q R b f n _).trans
    (associatorValueIso_hom_element A B C E F P Q R b c e f t q v hi hl hn)

end SerrePositivity.DifferentialGraded.BimoduleTensor
