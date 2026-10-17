module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoLocalizedFactorization
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# 逐次図式の境界分解で相対的な後続比較射が単射となる

## 概要
逐次図式の境界分解で相対的な後続比較射が単射となる。
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
[棚卸し m0554][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0554
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual relative boundary factorization of a natural-number diagram comparison

Each successor factors the actual relative pushout from the already
constructed previous middle object. Thus every earlier factor is kept.
No model structure or previously chosen diagram factorization is assumed.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.SequentialBoundaryFactorization
open MonoLocalizedFactorization
variable {F G : ℕ ⥤ SSet.{v}} (α : F ⟶ G)

abbrev stepMap (F : ℕ ⥤ SSet.{v}) (n : ℕ) := F.map (homOfLE (Nat.le_succ n))

structure Stage (n : ℕ) where
  obj : SSet.{v}
  i : F.obj n ⟶ obj
  p : obj ⟶ G.obj n
  fac : i ≫ p = α.app n
  hp : SSet.modelCategoryQuillen.I.rlp p

def initial : Stage α 0 where
  obj := middle (α.app 0)
  i := left (α.app 0)
  p := right (α.app 0)
  fac := fac _
  hp := factorization.hp _

def successorArrow (n : ℕ) (s : Stage α n) : pushout (stepMap F n) s.i ⟶ G.obj (n + 1) :=
  pushout.desc (α.app (n + 1)) (s.p ≫ stepMap G n) (by
    rw [← Category.assoc, s.fac]
    exact α.naturality _)

def successor (n : ℕ) (s : Stage α n) : Stage α (n + 1) where
  obj := middle (successorArrow α n s)
  i := pushout.inl _ _ ≫ left (successorArrow α n s)
  p := right (successorArrow α n s)
  fac := by
    rw [Category.assoc, fac]
    exact pushout.inl_desc _ _ _
  hp := factorization.hp _

def stage : ∀ n, Stage α n
  | 0 => initial α
  | n + 1 => successor α n (stage n)

abbrev transition (n : ℕ) : (stage α n).obj ⟶ (stage α (n + 1)).obj :=
  pushout.inr (stepMap F n) (stage α n).i ≫ left (successorArrow α n (stage α n))

lemma left_naturality (n : ℕ) :
    stepMap F n ≫ (stage α (n + 1)).i = (stage α n).i ≫ transition α n := by
  change stepMap F n ≫ (pushout.inl _ _ ≫ _) = _
  rw [← Category.assoc, pushout.condition, Category.assoc]

lemma right_naturality (n : ℕ) :
    transition α n ≫ (stage α (n + 1)).p = (stage α n).p ≫ stepMap G n := by
  change (pushout.inr _ _ ≫ left (successorArrow α n (stage α n))) ≫
    right (successorArrow α n (stage α n)) = _
  rw [Category.assoc, fac]
  exact pushout.inr_desc _ _ _

def diagram : ℕ ⥤ SSet.{v} := CategoryTheory.Functor.ofSequence (transition α)

def leftMap : F ⟶ diagram α := NatTrans.ofSequence (fun n => (stage α n).i) (by
  intro n
  dsimp only [diagram]
  rw [CategoryTheory.Functor.ofSequence_map_homOfLE_succ]
  exact left_naturality α n)

def rightMap : diagram α ⟶ G := NatTrans.ofSequence (fun n => (stage α n).p) (by
  intro n
  dsimp only [diagram]
  rw [CategoryTheory.Functor.ofSequence_map_homOfLE_succ]
  exact right_naturality α n)

lemma factorization_eq : leftMap α ≫ rightMap α = α := by
  apply NatTrans.ext
  funext n
  exact (stage α n).fac

lemma right_boundary_rlp (n : ℕ) : SSet.modelCategoryQuillen.I.rlp ((rightMap α).app n) :=
  (stage α n).hp

/-- 逐次図式の境界分解で相対的な後続比較射が単射となる。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
lemma relative_mono (n : ℕ) : Mono (left (successorArrow α n (stage α n))) := inferInstance

end SerrePositivity.SimplicialModel.SequentialBoundaryFactorization
