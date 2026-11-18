module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.EraseDifferentialMonoidal
public import SerrePositivity.EInfinity.BarrattEccles.Theory.AlgebraTransport
public import SerrePositivity.EInfinity.BarrattEccles.Theory.OperadMonoidalImage

/-!
# 微分を消した対称オペラッド

## 概要
Berger–Moerdijk 命題 4.1 のセル付加を扱うため、演算と代数の次数付き台を取る。

## 方針
各次数で元の演算と部分合成を使い、Koszul 対称性を保つ。

## 規約
零入力演算と単位を含む。

## 使われ方
セル代数の次数付き自由表示。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory HomologicalComplex DifferentialGraded
open Functor.LaxMonoidal

variable {A : Type u} [CommRing A]

/-- 微分を消したオペラッド。各 arity と部分合成を次数ごとに保つ。 -/
def Operad.erase (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A :=
  P.monoidalImage (eraseDifferential A)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
  export _root_.SerrePositivity.EInfinity.Operad (erase)

end SerrePositivity.EInfinity
