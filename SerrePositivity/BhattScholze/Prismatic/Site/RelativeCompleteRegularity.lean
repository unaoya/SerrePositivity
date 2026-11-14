module
public import SerrePositivity.BhattScholze.Delta.CompleteRegularity.RelativeCompleteRegularity
import all SerrePositivity.BhattScholze.Delta.CompleteRegularity.RelativeCompleteRegularity

public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
public import SerrePositivity.HomologicalAlgebra.KoszulAlgebraTorComparison
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Koszul.Complete
import Mathlib.Algebra.Module.Torsion.Basic

/-!
# 古典環の相対完全正則性

## 概要
BS 著者版 Definition 2.42 の古典環の場合を、通常の Koszul ホモロジーで表す。

## 方針
係数拡大と列の付加から Koszul 複体の標準射を作る。零次の平坦性と、
高次での剰余環上のテンソル比較を要求する。

## 規約
有限列を指定する。導来完備性は指定列の各元に関して課す。

## 使われ方
向き付き prism の係数環に対する prismatic envelope の入力条件。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.BhattScholze.Prismatic

open CategoryTheory DerivedCompletion
open scoped TensorProduct

variable {A B : Type u} [CommRing A] [CommRing B]
variable [Algebra A B] {n r : ℕ}

local notation "z[" a "," x "]" => appendKoszulCoordinates (algebraMap _ _ ∘ a) x

/-- BS 著者版 Definition 2.42 の (p,d) への特殊化。 -/
@[expose] def IsPrismCompletelyRegularRel {p : ℕ} [Fact p.Prime] (P : OrientedPrism p A)
    (x : Fin r → B) : Prop :=
  IsCompletelyRegularRel ![(p : A), P.generator] x

end SerrePositivity.BhattScholze.Prismatic
