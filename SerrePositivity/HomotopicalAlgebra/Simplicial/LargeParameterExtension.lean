module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftFillers
public import SerrePositivity.HomotopicalAlgebra.Simplicial.SkeletalCellGluing
public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeChoiceSpace

/-!
# 小さい比較空間の宇宙liftを値として大きいパラメータ上の指定族を相対延長する

## 概要
小さい比較空間の宇宙liftを値として大きいパラメータ上の指定族を相対延長する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。

## 規約と注意
モデル構造と射クラスの一致を要求する入口では、その指定データを仮定する。
このファイルがHT-KQの引用モデルを自動的に選ぶとは解釈しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0441][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0441
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Large parameters with values in a universe lift of a small comparison space

Only small boundary fillers are required. The actual skeletal pushouts in
the larger universe assemble them into one extension. No model structure
in that larger universe is assumed.
-/

@[expose] public section
universe w v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.SimplicialModel.LargeParameterExtension
variable {P : SSet.{v}} (hp : UniverseLift.BoundaryFillers P)
  {A K : SSet.{max w v}} (j : A ⟶ K) [Mono j]

def rule : SkeletalCellGluing.Rule (Q := UniverseLift.obj.{w} P) j := by
  intro n a c
  let ex := UniverseLift.boundaryFillers hp n (SkeletalCellGluing.boundary j c ≫ a)
  exact ⟨ex.choose, ex.choose_spec⟩

def extend (a : A ⟶ UniverseLift.obj.{w} P) : K ⟶ UniverseLift.obj.{w} P :=
  SkeletalCellGluing.assemble j (rule hp j) a

@[reassoc]
lemma extend_initial (a : A ⟶ UniverseLift.obj.{w} P) : j ≫ extend hp j a = a :=
  SkeletalCellGluing.assemble_initial _ _ _

@[reassoc]
lemma extend_prescribed (a : A ⟶ UniverseLift.obj.{w} P) {L : SSet.{max w v}} (s : L ⟶ A) :
    (s ≫ j) ≫ extend hp j a = s ≫ a := by rw [Category.assoc, extend_initial]

section Relative
variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {V T Q : SSet.{v}} (i : V ⟶ T) [Mono i] (b : V ⟶ Q)
  (p : Q ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
  (hq : trivialFibrations SSet.{v} p)

include hcof hfib hq in
lemma relativeFillers : UniverseLift.BoundaryFillers (RelativeChoiceSpace.obj i b) :=
  fun n a => RelativeChoiceSpace.extension hcof hfib i b p hq (SSet.boundary.{v} n).ι a

/-- 小さい比較空間の宇宙liftを値として大きいパラメータ上の指定族を相対延長する。

モデル構造と射クラスの一致を要求する入口では、その指定データを仮定する。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
def relativeExtend {A K : SSet.{max w v}} (j : A ⟶ K) [Mono j]
    (a : A ⟶ UniverseLift.obj.{w} (RelativeChoiceSpace.obj i b)) :
    K ⟶ UniverseLift.obj.{w} (RelativeChoiceSpace.obj i b) :=
  extend (relativeFillers hcof hfib i b p hq) j a

@[reassoc]
lemma relativeExtend_initial {A K : SSet.{max w v}} (j : A ⟶ K) [Mono j]
    (a : A ⟶ UniverseLift.obj.{w} (RelativeChoiceSpace.obj i b)) :
    j ≫ relativeExtend hcof hfib i b p hq j a = a :=
  extend_initial _ _ _

end Relative
end SerrePositivity.SimplicialModel.LargeParameterExtension
