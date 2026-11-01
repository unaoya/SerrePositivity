module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.DegenerateHornInput
public import SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryCotensor

/-!
# 中断した任意モデル源への一般化：NaturalHornFilling

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Transpose one horn filling operation into strictly natural parameter families。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0455][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0455
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Transpose one horn filling operation into strictly natural parameter families

The chosen operation lives in the original target K, independently of
the source parameter T. The resulting actual T-tensored fillers commute
strictly with every change of T. Prescribed degeneracy inputs remain
prescribed after this transposition.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.NaturalHornFilling
open BoundaryCotensor

lemma transpose_precompose {T U A K : SSet.{v}} (j : U ⟶ T) (f : T ⟶ (ihom A).obj K) :
    transpose (j ≫ f) = transpose f ≫ (pre j).app K := by
  apply transpose_injective
  rw [transpose_transpose, transpose_restriction, transpose_transpose]

variable (K : SSet.{v}) {n : ℕ} (i : Fin (n + 2))
  (s : (ihom (SSet.horn (n + 1) i).toSSet).obj K ⟶
    (ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).obj K)
  {T : SSet.{v}} (b : (SSet.horn (n + 1) i).toSSet ⟶ (ihom T).obj K)

abbrev fill : SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ⟶ (ihom T).obj K :=
  transpose (transpose b ≫ s)

lemma fill_restriction (hs : s ≫ KanHornFamilyLifting.restriction K i = 𝟙 _) :
    (SSet.horn (n + 1) i).ι ≫ fill K i s b = b := by
  apply transpose_injective
  rw [transpose_precompose, fill, transpose_transpose, Category.assoc, hs, Category.comp_id]

lemma fill_reindex {U : SSet.{v}} (j : U ⟶ T) :
    fill K i s (b ≫ (pre j).app K) = fill K i s b ≫ (pre j).app K := by
  change transpose (transpose (b ≫ (pre j).app K) ≫ s) = _
  rw [transpose_restriction, Category.assoc]
  exact transpose_precompose j (transpose b ≫ s)

abbrev family : T ⊗ SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ⟶ K :=
  uncurry (fill K i s b)

lemma family_reindex {U : SSet.{v}} (j : U ⟶ T) :
    family K i s (b ≫ (pre j).app K) =
      j ▷ SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ≫ family K i s b := by
  rw [family, fill_reindex]
  exact uncurry_pre_app K (fill K i s b) j

lemma fill_degenerate (d : Fin (n + 1))
    (e : SSet.stdSimplex.obj (SimplexCategory.mk n) ⟶ (ihom T).obj K)
    (hd : DegenerateHornInput.boundary i d K ≫ s = DegenerateHornInput.degeneracy d K) :
    fill K i s ((SSet.horn (n + 1) i).ι ≫ SSet.stdSimplex.σ d ≫ e) =
      SSet.stdSimplex.σ d ≫ e := by
  apply transpose_injective
  rw [fill, transpose_transpose]
  have hb : transpose ((SSet.horn (n + 1) i).ι ≫ SSet.stdSimplex.σ d ≫ e) =
      transpose e ≫ DegenerateHornInput.boundary i d K := by
    rw [transpose_precompose, transpose_precompose]
    rfl
  rw [hb, Category.assoc, hd]
  exact (transpose_precompose (SSet.stdSimplex.σ d) e).symm

end SerrePositivity.SimplicialModel.NaturalHornFilling
