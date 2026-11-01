module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.SequentialBoundaryFactorization
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanLocalizedLeftProper
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanTestLiftingClass

/-!
# 逐次比較の相対後続因子が指定した左持ち上げクラスに属する

## 概要
逐次比較の相対後続因子が指定した左持ち上げクラスに属する。
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
[棚卸し m0556][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0556
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Relative successor factors of a sequential localized equivalence

Only the source successor maps are assumed mono. The actual relative
factor constructed at each successor lies in the fixed Kan-test left
lifting class, not merely in an objectwise weak class.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.SequentialFactorLiftingClasses
open SequentialBoundaryFactorization MonoLocalizedFactorization KanTestLiftingClass
variable {F G : ℕ ⥤ SSet.{v}} (α : F ⟶ G)

instance left_mono (n : ℕ) : Mono (stage α n).i := by
  induction n with
  | zero => change Mono (left (α.app 0)); infer_instance
  | succ n ih =>
    have : Mono (stage α n).i := ih
    have : Mono (pushout.inl (stepMap F n) (stage α n).i) :=
      (MorphismProperty.monomorphisms SSet.{v}).pushout_inl _ _ inferInstance
    change Mono (pushout.inl _ _ ≫ left (successorArrow α n (stage α n)))
    infer_instance

lemma right_localized_isIso (n : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map (stage α n).p) := by
  have h := (stage α n).hp
  rw [← SSet.rlp_monomorphisms] at h
  exact MonoRightLiftingContraction.localized_isIso _ h

lemma left_localized_isIso (n : ℕ) (hα : IsIso (AnodyneHomotopy.anodyneQ.map (α.app n))) :
    IsIso (AnodyneHomotopy.anodyneQ.map (stage α n).i) := by
  have : IsIso (AnodyneHomotopy.anodyneQ.map (stage α n).p) := right_localized_isIso α n
  have h := congrArg AnodyneHomotopy.anodyneQ.map (stage α n).fac
  rw [CategoryTheory.Functor.map_comp] at h
  exact (isIso_comp_right_iff _ _).mp (h.symm ▸ hα)

lemma initial_llp (hα : IsIso (AnodyneHomotopy.anodyneQ.map (α.app 0))) :
    rightTests.llp (stage α 0).i :=
  localizedMono_le_llp _ ⟨inferInstance, left_localized_isIso α 0 hα⟩

/-- 逐次比較の相対後続因子が指定した左持ち上げクラスに属する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
lemma relative_llp (n : ℕ) [Mono (stepMap F n)]
    (hα : ∀ n, IsIso (AnodyneHomotopy.anodyneQ.map (α.app n))) :
    rightTests.llp (left (successorArrow α n (stage α n))) := by
  let t := pushout.inl (stepMap F n) (stage α n).i
  have ht : IsIso (AnodyneHomotopy.anodyneQ.map t) :=
    KanLocalizedLeftProper.localized_isIso (stage α n).i (left_localized_isIso α n (hα n))
      (stepMap F n) (pushout.inr _ _) t (IsPushout.of_hasPushout _ _).flip
  have he : t ≫ left (successorArrow α n (stage α n)) = (stage α (n + 1)).i := rfl
  have h := congrArg AnodyneHomotopy.anodyneQ.map he
  rw [CategoryTheory.Functor.map_comp] at h
  have : IsIso (AnodyneHomotopy.anodyneQ.map t) := ht
  have hw : IsIso (AnodyneHomotopy.anodyneQ.map (left (successorArrow α n (stage α n)))) :=
    (isIso_comp_left_iff _ _).mp (h.symm ▸ left_localized_isIso α (n + 1) (hα (n + 1)))
  exact localizedMono_le_llp _ ⟨inferInstance, hw⟩

end SerrePositivity.SimplicialModel.SequentialFactorLiftingClasses
