module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.CompatibleInputMap
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NormalizedHornTargetComparison

/-!
# 中断した任意モデル源への一般化：NormalizedHornInputMap

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Degenerate horn input unions are strictly functorial in the target。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0499][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0499
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Degenerate horn input unions are strictly functorial in the target
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.NormalizedHornInputMap
variable {K L M : SSet.{v}} {n : ℕ} (i : Fin (n + 2)) (q : K ⟶ L)

lemma boundary_naturality (d : Fin (n + 1)) : DegenerateHornInput.boundary i d K ≫
    (ihom (SSet.horn (n + 1) i).toSSet).map q =
    (ihom (SSet.stdSimplex.obj (SimplexCategory.mk n))).map q ≫
      DegenerateHornInput.boundary i d L := by
  dsimp only [DegenerateHornInput.boundary, DegenerateHornInput.degeneracy,
    KanHornFamilyLifting.restriction]
  rw [Category.assoc, ← (pre (SSet.horn (n + 1) i).ι).naturality q,
    ← Category.assoc, ← (pre (SSet.stdSimplex.σ d)).naturality q, Category.assoc]

def map : (NormalizedHornTargetComparison.inputs (K := K) i).toSSet ⟶
    (NormalizedHornTargetComparison.inputs (K := L) i).toSSet :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompatibleInputMap.map
    (fun _ : Fin (n + 1) => (ihom (SSet.stdSimplex.obj (SimplexCategory.mk n))).obj K)
    (fun _ : Fin (n + 1) => (ihom (SSet.stdSimplex.obj (SimplexCategory.mk n))).obj L)
    (fun d => DegenerateHornInput.boundary i d K)
    (fun d => DegenerateHornInput.boundary i d L)
    ((ihom (SSet.horn (n + 1) i).toSSet).map q)
    (fun _ => (ihom (SSet.stdSimplex.obj (SimplexCategory.mk n))).map q)
    (boundary_naturality i q)

lemma map_inclusion : map i q ≫ (NormalizedHornTargetComparison.inputs (K := L) i).ι =
    (NormalizedHornTargetComparison.inputs (K := K) i).ι ≫
      (ihom (SSet.horn (n + 1) i).toSSet).map q := rfl

lemma map_id : map i (𝟙 K) = 𝟙 _ := by
  apply (cancel_mono (NormalizedHornTargetComparison.inputs (K := K) i).ι).mp
  rw [map_inclusion, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]

lemma map_comp (r : L ⟶ M) : map i q ≫ map i r = map i (q ≫ r) := by
  apply (cancel_mono (NormalizedHornTargetComparison.inputs (K := M) i).ι).mp
  rw [Category.assoc, map_inclusion, ← Category.assoc, map_inclusion,
    map_inclusion, CategoryTheory.Functor.map_comp, Category.assoc]

end SerrePositivity.SimplicialModel.NormalizedHornInputMap
