module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.Generators
public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightLiftingContraction

/-!
# モデル構造不要の関手的単射分解の右因子はすべての単射に対する右持ち上げ性を持つ

## 概要
モデル構造不要の関手的単射分解の右因子はすべての単射に対する右持ち上げ性を持つ。
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
[棚卸し m0451][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0451
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# A model-free functorial mono factorization with a localized-equivalence right factor

Only the original boundary small-object argument is used. Every right
factor has an actual section and a vertical contraction, in the same
value universe. No Kan condition is imposed on the arrow's endpoints.
-/

@[expose] public section
universe v
noncomputable section
open CategoryTheory

namespace SerrePositivity.SimplicialModel.MonoLocalizedFactorization

def factorization : MorphismProperty.FunctorialFactorizationData
    (MorphismProperty.monomorphisms SSet.{v}) SSet.modelCategoryQuillen.I.rlp := by
  rw [← boundaryGenerators_leftClass]
  let : SSet.modelCategoryQuillen.I.{v}.HasSmallObjectArgument.{v} :=
    boundaryGenerators_smallObjectArgument
  exact MorphismProperty.functorialFactorizationData _ _

abbrev middle {A B : SSet.{v}} (f : A ⟶ B) : SSet.{v} := factorization.Z.obj (Arrow.mk f)
abbrev left {A B : SSet.{v}} (f : A ⟶ B) : A ⟶ middle f :=
  factorization.i.app (Arrow.mk f)
abbrev right {A B : SSet.{v}} (f : A ⟶ B) : middle f ⟶ B :=
  factorization.p.app (Arrow.mk f)

lemma fac {A B : SSet.{v}} (f : A ⟶ B) : left f ≫ right f = f :=
  factorization.fac_app

instance left_mono {A B : SSet.{v}} (f : A ⟶ B) : Mono (left f) := factorization.hi _

/-- モデル構造不要の関手的単射分解の右因子はすべての単射に対する右持ち上げ性を持つ。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
lemma right_all_mono_rlp {A B : SSet.{v}} (f : A ⟶ B) :
    (MorphismProperty.monomorphisms SSet.{v}).rlp (right f) := by
  rw [SSet.rlp_monomorphisms]
  exact factorization.hp _

lemma right_localized_isIso {A B : SSet.{v}} (f : A ⟶ B) :
    IsIso (AnodyneHomotopy.anodyneQ.map (right f)) :=
  MonoRightLiftingContraction.localized_isIso _ (right_all_mono_rlp f)

lemma left_localized_isIso_iff {A B : SSet.{v}} (f : A ⟶ B) :
    IsIso (AnodyneHomotopy.anodyneQ.map (left f)) ↔
      IsIso (AnodyneHomotopy.anodyneQ.map f) := by
  have : IsIso (AnodyneHomotopy.anodyneQ.map (right f)) := right_localized_isIso f
  have he := congrArg AnodyneHomotopy.anodyneQ.map (fac f)
  rw [CategoryTheory.Functor.map_comp] at he
  rw [← he]
  exact (isIso_comp_right_iff (AnodyneHomotopy.anodyneQ.map (left f))
    (AnodyneHomotopy.anodyneQ.map (right f))).symm

end SerrePositivity.SimplicialModel.MonoLocalizedFactorization
