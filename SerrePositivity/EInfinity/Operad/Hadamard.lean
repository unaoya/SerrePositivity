module

public import SerrePositivity.EInfinity.Operad.HadamardAssociativity
public import SerrePositivity.EInfinity.Operad.Morphism

/-!
# Arity ごとのテンソルオペラッド

概要：Berger–Moerdijk §1、Berger–Fresse §1.1.4 の Hopf 対角の終域を構成する。
方針：arity ごとのテンソルに単位・等変性・二種類の結合則を束ねる。
規約：arity 0 を含む対称 dg オペラッドで、符号は既存の Koszul 対称性に従う。
使われ方：Barratt–Eccles の AW 対角をオペラッド射として定式化する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.Operad

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A]

/-- 概要：二つの対称 dg オペラッドの Hadamard 積（Berger–Moerdijk §1）。
方針：各 arity のテンソルに tensorμ を介した部分合成を与える。
規約：単位・二つの等変性・入れ子と独立な合成の結合則を全て含む。
使われ方：Hopf オペラッドの対角射の終域となる。 -/
def hadamard (P Q : Operad A) : Operad A where
  sequence := Hadamard.sequence P Q
  unit := Hadamard.unit P Q
  comp := Hadamard.comp P Q
  unit_comp := Hadamard.unit_comp P Q
  comp_unit := Hadamard.comp_unit P Q
  inner_equivariance := Hadamard.inner_equivariance P Q
  outer_equivariance := Hadamard.outer_equivariance P Q
  nested_assoc m n k i j := by
    rw [Hadamard.transport P Q (Nat.add_assoc m n k).symm]
    exact Hadamard.nested_assoc P Q m n k i j
  parallel_assoc m n k i j hij := by
    rw [Hadamard.transport_right P Q (by omega : m + 1 + n = m + n + 1),
      Hadamard.transport_right P Q (by omega : m + 1 + k = m + k + 1),
      Hadamard.transport P Q (by omega : m + k + n = m + n + k)]
    exact Hadamard.parallel_assoc P Q m n k i j hij

end SerrePositivity.EInfinity.Operad
