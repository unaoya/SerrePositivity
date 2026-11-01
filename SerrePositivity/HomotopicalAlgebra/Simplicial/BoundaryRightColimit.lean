module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.Generators
public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightLiftingContraction
public import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleLiftingClosure
public import Mathlib.CategoryTheory.Category.ULift

/-!
# 境界に対する右持ち上げ性がfilteredな余極限で保たれる

## 概要
境界に対する右持ち上げ性がfilteredな余極限で保たれる。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論の加法性・局所化で現れる貼り合わせと余極限の比較に利用できる。
[棚卸し m0357][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0357
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Filtered and sequential colimits of actual boundary-right arrows

Finite presentability of both endpoints of each boundary generator gives
the lifting property on the original colimit. A lifted index category
handles actual natural-number diagrams in any value universe.
-/

@[expose] public section
universe v
noncomputable section
open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen
attribute [local instance] Cardinal.fact_isRegular_aleph0

namespace SerrePositivity.SimplicialModel.BoundaryRightColimit

/-- 境界に対する右持ち上げ性がfilteredな余極限で保たれる。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
lemma filtered_rlp {J : Type v} [SmallCategory J] [IsFiltered J]
    {F : J ⥤ Arrow SSet.{v}} {c : Cocone F} (hc : IsColimit c)
    (hF : ∀ j, I.rlp (F.obj j).hom) : I.rlp c.pt.hom := by
  have : IsCardinalFiltered J Cardinal.aleph0.{v} :=
    (isCardinalFiltered_aleph0_iff J).mpr inferInstance
  have hdom : ∀ i : I.{v}.toSet, IsCardinalPresentable i.val.left Cardinal.aleph0.{v} := by
    rintro ⟨f, hf⟩
    rcases f with ⟨A, B, f⟩
    cases hf with
    | mk n =>
      change IsCardinalPresentable (SSet.boundary.{v} n).toSSet Cardinal.aleph0.{v}
      infer_instance
  have hcod : ∀ i : I.{v}.toSet, IsCardinalPresentable i.val.right Cardinal.aleph0.{v} := by
    rintro ⟨f, hf⟩
    rcases f with ⟨A, B, f⟩
    cases hf with
    | mk n =>
      change IsCardinalPresentable (SSet.stdSimplex.{v}.obj (SimplexCategory.mk n))
        Cardinal.aleph0.{v}
      infer_instance
  exact @Smith.AccessibleLiftingClosure.rlp_of_isColimit.{v, v, v + 1}
    SSet.{v} _ _ I.{v} Cardinal.aleph0.{v} _ hdom hcod J _ _ F c hc hF

lemma sequential_rlp {F : ℕ ⥤ Arrow SSet.{v}} {c : Cocone F} (hc : IsColimit c)
    (hF : ∀ n, I.rlp (F.obj n).hom) : I.rlp c.pt.hom := by
  let e := (AsSmall.equiv.{0, 0, v} (C := ℕ)).symm
  have : IsFiltered (AsSmall.{v} ℕ) := IsFiltered.of_equivalence (AsSmall.equiv.{0, 0, v} (C := ℕ))
  exact filtered_rlp (J := AsSmall.{v} ℕ) (F := e.functor ⋙ F)
    (c := c.whisker e.functor) (hc.whiskerEquivalence e) (fun n => hF (e.functor.obj n))

lemma sequential_localized_isIso {F : ℕ ⥤ Arrow SSet.{v}} {c : Cocone F} (hc : IsColimit c)
    (hF : ∀ n, I.rlp (F.obj n).hom) :
    IsIso (AnodyneHomotopy.anodyneQ.map c.pt.hom) := by
  have h := sequential_rlp hc hF
  rw [← SSet.rlp_monomorphisms] at h
  exact MonoRightLiftingContraction.localized_isIso _ h

end SerrePositivity.SimplicialModel.BoundaryRightColimit
