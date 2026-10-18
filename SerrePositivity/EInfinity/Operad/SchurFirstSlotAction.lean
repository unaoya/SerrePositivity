module

public import SerrePositivity.EInfinity.Operad.FirstSlotPowerAction
public import SerrePositivity.EInfinity.Operad.SchurFirstBlockGenerator
public import SerrePositivity.EInfinity.Operad.SchurGeneratorExt

/-!
# 一般の Schur 入力上の先頭の結合則

概要：Berger–Moerdijk §1 の先頭の部分合成と二段の作用の一致を一般の入力へ拡張する。
方針：有限族から得られる先頭の入力作用を生成射上で計算し、余極限の一意性を使う。
規約：ここでは有限族から移送した入力射 firstSlotPowerAction を使う。
使われ方：既存の任意位置のテンソル代入射へ比較して自由代数の部分合成則を得る。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.Operad

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] tensorFamily SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：内側の Schur 演算の先頭代入の生成射は一般の先頭の入力作用で計算できる（Berger–Moerdijk §1）。
方針：先頭の入力作用を生成射上で計算し、内側の作用の生成射上の計算則を使う。
規約：内側の入力数 n と残る入力数 m は零でもよい。
使われ方：先頭ブロックの結合則の右辺を一般の入力射へ移す。 -/
lemma schurFirstBlockInputs_firstSlot (P : Operad A) (K : Complex A)
    (n m : ℕ) (s : Fin (n + m) → ℕ) :
    P.schurFirstBlockInputs K n m s ≫
      P.schurInputGenerator K (1 + m) (firstBlockArities n m s) =
    (P.arity n ◁ P.schurInputGenerator K (n + m) s) ≫
      firstSlotPowerAction ((schurFunctor A P.sequence).obj K) (P.arity n) n m
        (P.schurAction K n) := by
  rw [P.schurFirstBlockInputs_generator]
  have h := firstSlotPowerAction_generators ((schurFunctor A P.sequence).obj K) (P.arity n)
    (fun r => P.arity r ⊗ power K r) (fun r => schurι A P.sequence K r)
    n m (P.schurAction K n) s
  erw [P.schurInputGenerator_action] at h
  exact h.symm

/-- 概要：一般の Schur 入力上で先頭の部分合成と二段の作用は一致する（Berger–Moerdijk §1）。
方針：入力生成射で射を比較し、先頭ブロックの作用の式と一般の先頭入力作用の計算則を使う。
規約：入力射は有限族の分離と再結合から定義した firstSlotPowerAction。
使われ方：標準のテンソル代入射との比較後に自由代数の先頭での代数公理となる。 -/
lemma schurAction_firstSlot (P : Operad A) (K : Complex A) (m n : ℕ) :
    (P.composeAheadOfInputs m 0 n ▷ power ((schurFunctor A P.sequence).obj K) (n + m)) ≫
      P.schurAction K (n + m) =
    (α_ (P.arity (1 + m)) (P.arity n)
      (power ((schurFunctor A P.sequence).obj K) (n + m))).hom ≫
      (P.arity (1 + m) ◁
        firstSlotPowerAction ((schurFunctor A P.sequence).obj K) (P.arity n) n m
          (P.schurAction K n)) ≫
      P.schurAction K (1 + m) := by
  apply P.schurInputGenerator_hom_ext K (n + m) (P.arity (1 + m) ⊗ P.arity n)
    ((schurFunctor A P.sequence).obj K)
  intro s
  erw [whisker_exchange_assoc]
  rw [associator_naturality_right_assoc, ← whiskerLeft_comp_assoc,
    ← P.schurFirstBlockInputs_firstSlot]
  exact P.schurAction_firstBlock_generators K m n s

end SerrePositivity.EInfinity.Operad
