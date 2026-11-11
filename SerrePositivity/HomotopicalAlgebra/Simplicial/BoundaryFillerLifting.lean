module
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

public import SerrePositivity.HomotopicalAlgebra.Simplicial.LargeParameterExtension

/-!
# 全次元の境界充填からすべての単射に対する右持ち上げ性を導く

## 概要
全次元の境界充填からすべての単射に対する右持ち上げ性を導く。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0353][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0353
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# All-monomorphism lifting from boundary fillers without any model structure
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.BoundaryFillerLifting
variable {P : SSet.{v}} (hp : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.BoundaryFillers P)
  {A K : SSet.{v}} (j : A ⟶ K) [Mono j]

def rule : SkeletalCellGluing.Rule (Q := P) j := by
  intro n a c
  let ex := hp n (SkeletalCellGluing.boundary j c ≫ a)
  exact ⟨ex.choose, ex.choose_spec⟩

def extend (a : A ⟶ P) : K ⟶ P := SkeletalCellGluing.assemble j (rule hp j) a

@[reassoc]
lemma extend_initial (a : A ⟶ P) : j ≫ extend hp j a = a :=
  SkeletalCellGluing.assemble_initial _ _ _

include hp in
/-- 全次元の境界充填からすべての単射に対する右持ち上げ性を導く。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
lemma terminal_rightLifting : (MorphismProperty.monomorphisms SSet.{v}).rlp
    (SSet.stdSimplex.isTerminalObj₀.from P) := by
  intro A K j hj
  have : Mono j := hj
  constructor
  intro a _b sq
  exact CommSq.HasLift.mk'
    { l := extend hp j a
      fac_left := extend_initial hp j a
      fac_right := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _ }

end SerrePositivity.SimplicialModel.BoundaryFillerLifting
