module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SmallActionClosure
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization

/-!
# 小さい支配対象から得た部分複体の包含が指定局所化で可逆となる

## 概要
小さい支配対象から得た部分複体の包含が指定局所化で可逆となる。
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
[棚卸し m0572][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0572
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# A small homotopy-equivalent subcomplex from an actual small domination

Closing the image of the dominating map under the whole homotopy retains
both inverse homotopies. No model structure or ambient smallness is used.
-/

@[expose] public section
universe v w uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.SimplicialModel.SmallDominatedSubcomplex
variable {X K : SSet.{w}} (s : K ⟶ X) (q : X ⟶ K)
  (H : SSet.Homotopy (𝟙 X) (q ≫ s)) (A : X.Subcomplex)

abbrev complex : X.Subcomplex :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SmallActionClosure.closure H.h (A ⊔ Subfunctor.range s)

lemma seed_le : A ≤ complex s q H A :=
  le_sup_left.trans (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SmallActionClosure.le_closure H.h _)

def inside : K ⟶ (complex s q H A).toSSet :=
  Subfunctor.lift s (le_sup_right.trans
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SmallActionClosure.le_closure H.h (A ⊔ Subfunctor.range s)))

lemma inside_inclusion : inside s q H A ≫ (complex s q H A).ι = s := rfl

def retraction : X ⟶ (complex s q H A).toSSet := q ≫ inside s q H A

lemma retraction_inclusion : retraction s q H A ≫ (complex s q H A).ι = q ≫ s := by
  rw [retraction, Category.assoc, inside_inclusion]

include H in
lemma small (hK : ∀ n, Small.{v} (K.obj n))
    (hA : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SmallActionClosure.IsSmall.{v} A) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SmallActionClosure.IsSmall.{v} (complex s q H A) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SmallActionClosure.closure_small
  · intro n
    infer_instance
  · intro n
    have := hK n
    have := hA n
    change Small.{v} ↥(A.obj n ∪ Set.range (s.app n))
    infer_instance

/-- The same whole homotopy restricts to the countable closure. -/
def restrictedHomotopy : SSet.Homotopy (𝟙 (complex s q H A).toSSet)
    ((complex s q H A).ι ≫ retraction s q H A) where
  h := Subfunctor.lift ((complex s q H A).ι ▷ _ ≫ H.h)
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SmallActionClosure.closed H.h (A ⊔ Subfunctor.range s))
  h₀ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f => f.app n x.val) H.h₀
  h₁ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f => f.app n x.val) H.h₁
  rel := by
    apply NatTrans.ext
    funext n
    exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property)

/-- 小さい支配対象から得た部分複体の包含が指定局所化で可逆となる。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
def inclusionImageIso {D : Type uD} [Category.{vD} D] (L : SSet.{w} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) : L.obj (complex s q H A).toSSet ≅ L.obj X where
  hom := L.map (complex s q H A).ι
  inv := L.map (retraction s q H A)
  hom_inv_id := (L.map_comp _ _).symm.trans
    ((AnodyneHomotopy.map_homotopy_eq L hL (restrictedHomotopy s q H A)).symm.trans
      (L.map_id _))
  inv_hom_id := by
    rw [← L.map_comp, retraction_inclusion]
    exact (AnodyneHomotopy.map_homotopy_eq L hL H).symm.trans (L.map_id _)

end SerrePositivity.SimplicialModel.SmallDominatedSubcomplex
