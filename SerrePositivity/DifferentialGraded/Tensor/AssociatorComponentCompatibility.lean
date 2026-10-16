module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorComponentTransport
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorRightTransport

/-! # 結合比較のLeft作用の三重生成元上の整合性 -/
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

/-- 左F作用と結合比較の三重生成元上での可換式。 -/
lemma associatorComponent_leftCochain_compatibility (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (c : C) (e : E) (f f' : F) {p k r s i m n : ℤ}
    (hi : r + s = i) (hm : k + i = m) (hn : m + p = n) (g : GradedHom A f f' p)
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s) :
    associatorValueComponent A B C E F P Q R b f' n
      ((associatorLeftCochain A B C E F P Q R b f f' p g).v m n hn
        (associatorLeftElement A B C E F P Q R b c e f (n := m) t q v hi hm)) =
    (associatorRightCochain A B C E F P Q R b f f' p g).v m n hn
      (associatorValueComponent A B C E F P Q R b f m
        (associatorLeftElement A B C E F P Q R b c e f (n := m) t q v hi hm)) := by
  have hkrm : (k + r) + s = m := by omega
  have hS := associatorValueComponent_element A B C E F P Q R b c e f
    (i := i) (l := k + r) (n := m) t q v hi rfl hm
  have hR := associatorRightCochain_element A B C E F P Q R b c e f f'
    (j := k + p) (l' := k + r + p) rfl hkrm rfl rfl hn g t q v
  have hL := associatorLeftComponent_transport A B C E F P Q R b c e f f'
    (j := k + p) (l := k + r + p) hi hm rfl (by omega) hn g t q v
  exact hL.trans ((congrArg (fun z =>
    (associatorRightCochain A B C E F P Q R b f f' p g).v m n hn z) hS).trans hR).symm

end SerrePositivity.DifferentialGraded.BimoduleTensor
