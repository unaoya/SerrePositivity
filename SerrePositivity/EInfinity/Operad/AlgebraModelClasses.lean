module

public import SerrePositivity.EInfinity.Operad.Basic
public import SerrePositivity.EInfinity.Operad.AlgebraTerminal
public import SerrePositivity.EInfinity.ProjectiveModel

/-!
# 忘却関手で定める代数のモデル的な射の類

概要：Berger–Moerdijk 命題 4.1 の転送に使う弱同値・fibration の類を指定する。
方針：底の擬同型と全次数全射の類を忘却関手に沿って引き戻す。
規約：モデル構造の存在は仮定せず、構造は局所的に選ぶ。
使われ方：path object と acyclicity の命題を転送の前に述べる。
-/

@[expose] public section

universe u

namespace SerrePositivity.EInfinity.Operad.Algebra

open CategoryTheory HomotopicalAlgebra HomologicalComplex
open SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A] (P : Operad A)

/-- 概要：代数の弱同値は底の複体の擬同型（BM 命題 4.1）。
方針：擬同型の類を忘却関手で引き戻す。
規約：大域 instance に登録しない。
使われ方：転送前に path object の弱同値条件を述べる。 -/
@[instance_reducible]
def weakEquivalenceStructure : CategoryWithWeakEquivalences P.Algebra where
  weakEquivalences := (quasiIso (ModuleCat A) (.up ℤ)).inverseImage (forget P)

/-- 概要：代数の fibration は底の全次数全射（BM 命題 4.1）。
方針：射影 fibration の類を忘却関手で引き戻す。
規約：大域 instance に登録しない。
使われ方：転送前に good path object の評価条件を述べる。 -/
@[instance_reducible]
def fibrationStructure : CategoryWithFibrations P.Algebra where
  fibrations := (projectiveFibrations A).inverseImage (forget P)

/-- 概要：零代数への射は底で射影 fibration（BM 命題 4.1）。
方針：各次数の零対象への射は全射であることを使う。
規約：代数の cofibrancy は要求しない。
使われ方：持ち上げ性から代数射の retraction を得る。 -/
lemma toTerminal_projectiveFibration (X : P.Algebra) :
    projectiveFibrations A (toTerminal P X).hom := by
  intro n
  have hz : Limits.IsZero (terminalAlgebra P).carrier := Limits.isZero_zero (Complex A)
  have hn := Functor.map_isZero (HomologicalComplex.eval (ModuleCat A) (.up ℤ) n) hz
  have := hn.epi ((toTerminal P X).hom.f n)
  exact (ModuleCat.epi_iff_surjective _).1 inferInstance

end SerrePositivity.EInfinity.Operad.Algebra
