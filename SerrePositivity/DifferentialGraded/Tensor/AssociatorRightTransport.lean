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

/-- 結合同型の後に左作用を適用した生成元の評価。 -/
lemma associatorRightCochain_transport (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (c : C) (e : E) (f f' : F) {p k r s i m n : ℤ}
    (hi : r + s = i) (hm : k + i = m) (hn : m + p = n) (g : GradedHom A f f' p)
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s) :
    (associatorRightCochain A B C E F P Q R b f f' p g).v m n hn
      ((associatorValueIso A B C E F P Q R b f).hom.f m
        (associatorLeftElement A B C E F P Q R b c e f (n := m) t q v hi hm)) =
    associatorRightElement A B C E F P Q R b c e f' (l := k + r + p) (n := n)
      (SerrePositivity.DifferentialGraded.leftAction A (R.leftAt e) g t rfl)
      q v (by omega) (by omega) := by
  have hS := associatorValueIso_hom_element A B C E F P Q R b c e f
    (i := i) (l := k + r) (n := m) t q v hi rfl hm
  have hR := associatorRightCochain_element A B C E F P Q R b c e f f'
    (j := k + p) (l' := k + r + p) rfl (by omega) rfl rfl hn g t q v
  exact (congrArg (fun z =>
    (associatorRightCochain A B C E F P Q R b f f' p g).v m n hn z) hS).trans hR

end SerrePositivity.DifferentialGraded.BimoduleTensor
