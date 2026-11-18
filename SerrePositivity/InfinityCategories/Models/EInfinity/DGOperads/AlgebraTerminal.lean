module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraLimitCriterion
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
模型。文献の定義との比較は後で
# オペラッド代数の終対象

概要：Berger–Moerdijk §1 のオペラッド代数の終対象を零複体上に構成する。
方針：空の共同単射族によって零作用の代数公理を判定する。
規約：零入力の作用も零写像であり、モデル構造は使わない。
使われ方：転送の acyclicity の証明で全代数の fibrancy を利用する。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.ZeroObject
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A] (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A)

/-- 概要：零複体上のオペラッド代数（BM §1）。
方針：全演算を零写像とし、零対象への射の一意性を使う。
規約：arity 0 の演算も含む。
使われ方：代数の圏の終対象を供給する。 -/
def terminalAlgebra : P.Algebra :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.ofJointlyMonicActions (0 : Complex A) (fun j : Empty => nomatch j)
    (fun j => nomatch j) (fun _ => 0) (by intro j; exact j.elim)
    (by intro T f g _; exact (isZero_zero (Complex A)).eq_of_tgt f g)

/-- 概要：任意の代数から零代数への一意な射（BM §1）。
方針：底の零写像の作用保存を零対象への射の一意性から得る。
規約：底の射は零複体への零写像。
使われ方：全対象の fibrancy と retraction の構成に用いる。 -/
def toTerminal (X : P.Algebra) : X ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.terminalAlgebra P where
  hom := 0
  comm _ := (isZero_zero (Complex A)).eq_of_tgt _ _

/-- 概要：零代数は代数の圏の終対象（BM §1）。
方針：底の複体への忘却の忠実性と零対象への射の一意性を使う。
規約：任意の可換係数環に適用する。
使われ方：転送に用いる代数の終対象の存在を保証する。 -/
def terminalAlgebraIsTerminal : IsTerminal (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.terminalAlgebra P) :=
  IsTerminal.ofUniqueHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.toTerminal P) (fun _ _ =>
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext ((isZero_zero (Complex A)).eq_of_tgt _ _))

/-- 概要：オペラッド代数の圏は終対象を持つ（BM §1）。
方針：零代数の終対象性を存在証明へ束ねる。
規約：モデル構造を大域的に登録しない。
使われ方：全対象の fibrancy を述べる。 -/
instance _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.instHasTerminal : HasTerminal P.Algebra := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.terminalAlgebraIsTerminal P).hasTerminal

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra
