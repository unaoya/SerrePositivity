module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentTetrahedronBoundary

/-!
概要：任意の単体集合の三単体の六辺の面間での同定。
方針：指定された単体の境界と既存の合成則を使う。
規約：辺と同型の値を新しく選択しない。
使われ方：全錐の比較円柱の三つの合成関係の照合。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：三単体の辺 13 の二つの面による表示は一致。
方針：二つの面の合成の単体恒等式を評価する。
規約：一次単体そのものの等式。
使われ方：四面の指定同型の境界関手を同定する。 -/
lemma tetrahedronEdge13_eq {X : SSet.{u}} (s : X _⦋3⦌) :
    X.δ 0 (X.δ 2 s) = X.δ 1 (X.δ 0 s) :=
  ConcreteCategory.congr_hom (X.δ_comp_δ (show (0 : Fin 3) ≤ 1 by decide)) s
/-- 概要：三単体の辺 03 の二つの面による表示は一致。
方針：二つの面の合成の単体恒等式を評価する。
規約：一次単体そのものの等式。
使われ方：四面の指定同型の境界関手を同定する。 -/
lemma tetrahedronEdge03_eq {X : SSet.{u}} (s : X _⦋3⦌) :
    X.δ 1 (X.δ 1 s) = X.δ 1 (X.δ 2 s) :=
  ConcreteCategory.congr_hom (X.δ_comp_δ_self (i := (1 : Fin 3))) s
/-- 概要：三単体の辺 02 の二つの面による表示は一致。
方針：二つの面の合成の単体恒等式を評価する。
規約：一次単体そのものの等式。
使われ方：四面の指定同型の境界関手を同定する。 -/
lemma tetrahedronEdge02_eq {X : SSet.{u}} (s : X _⦋3⦌) :
    X.δ 2 (X.δ 1 s) = X.δ 1 (X.δ 3 s) :=
  (ConcreteCategory.congr_hom (X.δ_comp_δ (show (1 : Fin 3) ≤ 2 by decide)) s).symm
/-- 概要：三単体の辺 23 の二つの面による表示は一致。
方針：二つの面の合成の単体恒等式を評価する。
規約：一次単体そのものの等式。
使われ方：四面の指定同型の境界関手を同定する。 -/
lemma tetrahedronEdge23_eq {X : SSet.{u}} (s : X _⦋3⦌) :
    X.δ 0 (X.δ 1 s) = X.δ 0 (X.δ 0 s) :=
  (ConcreteCategory.congr_hom (X.δ_comp_δ_self (i := (0 : Fin 3))) s).symm
/-- 概要：三単体の辺 01 の二つの面による表示は一致。
方針：二つの面の合成の単体恒等式を評価する。
規約：一次単体そのものの等式。
使われ方：四面の指定同型の境界関手を同定する。 -/
lemma tetrahedronEdge01_eq {X : SSet.{u}} (s : X _⦋3⦌) :
    X.δ 2 (X.δ 3 s) = X.δ 2 (X.δ 2 s) :=
  (ConcreteCategory.congr_hom (X.δ_comp_δ_self (i := (2 : Fin 3))) s).symm
/-- 概要：三単体の辺 12 の二つの面による表示は一致。
方針：二つの面の合成の単体恒等式を評価する。
規約：一次単体そのものの等式。
使われ方：四面の指定同型の境界関手を同定する。 -/
lemma tetrahedronEdge12_eq {X : SSet.{u}} (s : X _⦋3⦌) :
    X.δ 0 (X.δ 3 s) = X.δ 2 (X.δ 0 s) :=
  ConcreteCategory.congr_hom (X.δ_comp_δ (show (0 : Fin 3) ≤ 2 by decide)) s

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
