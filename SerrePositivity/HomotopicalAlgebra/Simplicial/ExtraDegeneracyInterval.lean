module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.CategoryTheory.Simplex.Prefix
public import SerrePositivity.CategoryTheory.Simplex.Naturality
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# 追加退化から実際の標準区間シリンダー上の写像を構成する

## 概要
追加退化から実際の標準区間シリンダー上の写像を構成する。
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
[棚卸し m0397][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0397
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# An extra degeneracy gives an actual map from the standard interval cylinder
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.SimplicialModel.ExtraDegeneracyInterval
variable {A : SimplicialObject.Augmented (Type v)}
  (ed : SimplicialObject.Augmented.ExtraDegeneracy A)

abbrev shifted : SSet.{v} := SimplexPrefix.functor.op ⋙ A.left

def extra : A.left ⟶ shifted (A := A) :=
  SimplexNaturality.ofFacesDegeneracies _ _ (fun n => ed.s n.unop.len)
    (by
      intro n i
      change A.left.δ i ≫ ed.s n = ed.s (n + 1) ≫
        A.left.map (SimplexPrefix.functor.map (SimplexCategory.δ i)).op
      rw [SimplexPrefix.map_δ]
      exact (ed.s_comp_δ n i).symm)
    (by
      intro n i
      change A.left.σ i ≫ ed.s (n + 1) = ed.s n ≫
        A.left.map (SimplexPrefix.functor.map (SimplexCategory.σ i)).op
      rw [SimplexPrefix.map_σ]
      exact (ed.s_comp_σ n i).symm)

/-- 追加退化から実際の標準区間シリンダー上の写像を構成する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
def intervalMap : A.left ⊗ SimplexPrefix.interval ⟶ A.left where
  app n := ↾fun x => A.left.map (SimplexPrefix.cut n.unop x.2).op ((extra ed).app n x.1)
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    have hs := types_congr_hom ((extra ed).naturality θ) x.1
    change (extra ed).app m (A.left.map θ x.1) =
      A.left.map (SimplexPrefix.functor.map θ.unop).op ((extra ed).app n x.1) at hs
    change A.left.map (SimplexPrefix.cut m.unop (SimplexPrefix.interval.map θ x.2)).op
      ((extra ed).app m (A.left.map θ x.1)) =
        A.left.map θ (A.left.map (SimplexPrefix.cut n.unop x.2).op ((extra ed).app n x.1))
    rw [hs]
    have h := congrArg (fun f => A.left.map f.op) (SimplexPrefix.cut_naturality θ.unop x.2)
    simp only [op_comp, A.left.map_comp] at h
    exact (types_congr_hom h ((extra ed).app n x.1)).symm

end SerrePositivity.SimplicialModel.ExtraDegeneracyInterval

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "4.7.2.9" (partial := component) "仮定：通常の集合値の増大単体的対象と追加退化（Lean が強い：集合値の増大単体的対象と指定した追加退化の場合）。結論：非負次数における shift への自然写像を構成し、追加退化と零番目の面との合成が恒等となる（分裂から section を得る向きの非負次数の成分）。増大対象全体の section との同値と逆向きは含まれない。"] _root_.SerrePositivity.SimplicialModel.ExtraDegeneracyInterval.extra
