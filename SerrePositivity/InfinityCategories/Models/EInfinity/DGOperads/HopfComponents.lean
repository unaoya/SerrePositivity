module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Hopf

/-!
模型。文献の定義との比較は後で
# Hopf 対角の成分の明示的な型

概要：Berger–Fresse §1.1.4 の対角を同じ arity の二重テンソルへの射として公開する。
方針：Hadamard 積の対称列への射の成分を取り出す。
規約：元の対角と定義上同じ射を用いる。
使われ方：convolution の構造射を比較するときに係数の終域の展開を局所化する。
-/

@[expose] public section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}

/-- 概要：Hopf 対角の arity 成分（BF §1.1.4）。
方針：自然変換の成分を明示的な二重テンソルの型で包む。
規約：余結合性・余単位のデータは元の Hopf 構造のもの。
使われ方：一般の convolution 図式の係数に特殊化する。 -/
def diagonalComponent (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P) (n : ℕ) : P.arity n ⟶ P.arity n ⊗ P.arity n :=
  hP.diagonal.map.app (_root_.SerrePositivity.FiniteBijection.of n)

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf
