module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.HadamardAssociativity
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Morphism

/-!
模型。文献の定義との比較は後で
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

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A]

/-- 概要：二つの対称 dg オペラッドの Hadamard 積（Berger–Moerdijk §1）。
方針：各 arity のテンソルに tensorμ を介した部分合成を与える。
規約：単位・二つの等変性・入れ子と独立な合成の結合則を全て含む。
使われ方：Hopf オペラッドの対角射の終域となる。 -/
def hadamard (P Q : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A where
  sequence := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.sequence P Q
  unit := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.unit P Q
  comp := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.comp P Q
  unit_comp := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.unit_comp P Q
  comp_unit := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.comp_unit P Q
  inner_equivariance := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.inner_equivariance P Q
  outer_equivariance := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.outer_equivariance P Q
  nested_assoc m n k i j := by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.transport P Q (Nat.add_assoc m n k).symm]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.nested_assoc P Q m n k i j
  parallel_assoc m n k i j hij := by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.transport_right P Q (by omega : m + 1 + n = m + n + 1),
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.transport_right P Q (by omega : m + 1 + k = m + k + 1),
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.transport P Q (by omega : m + k + n = m + n + k)]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.parallel_assoc P Q m n k i j hij

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
