module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.KanHornFamilyLifting

/-!
# 中断した任意モデル源への一般化：RelativeHornFillingOperation

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：One uniform horn filling operation preserves an entire prescribed input family。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0543][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0543
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# One uniform horn filling operation preserves an entire prescribed input family

A monomorphism into the space of horn boundaries supplies the normalized
inputs. The prescribed fillers are extended to one simplicial section
of restriction. Pulling this same section along any parameter map is
strictly natural and retains the prescribed whole fillers.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.RelativeHornFillingOperation
variable (K : SSet.{v}) {n : ℕ} (i : Fin (n + 2))
  (hK : SSet.modelCategoryQuillen.J.rlp (CategoryTheory.Limits.terminal.from K))
  {S : SSet.{v}} (b : S ⟶ (ihom (SSet.horn (n + 1) i).toSSet).obj K) [Mono b]
  (a : S ⟶ (ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).obj K)
  (ha : a ≫ KanHornFamilyLifting.restriction K i = b)

abbrev section_ := (KanHornFamilyLifting.relativeLift K i hK b (𝟙 _) a
  (by rw [Category.comp_id]; exact ha)).val

lemma section_restriction : section_ K i hK b a ha ≫ KanHornFamilyLifting.restriction K i =
    𝟙 _ := (KanHornFamilyLifting.relativeLift K i hK b (𝟙 _) a _).property.2

lemma section_prescribed : b ≫ section_ K i hK b a ha = a :=
  (KanHornFamilyLifting.relativeLift K i hK b (𝟙 _) a _).property.1

variable {L : SSet.{v}} (boundary : L ⟶ (ihom (SSet.horn (n + 1) i).toSSet).obj K)

abbrev fill : L ⟶ (ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).obj K :=
  boundary ≫ section_ K i hK b a ha

lemma fill_restriction : fill K i hK b a ha boundary ≫ KanHornFamilyLifting.restriction K i =
    boundary := by
  rw [fill, Category.assoc, section_restriction, Category.comp_id]

lemma fill_naturality {U : SSet.{v}} (j : U ⟶ L) :
    fill K i hK b a ha (j ≫ boundary) = j ≫ fill K i hK b a ha boundary :=
  Category.assoc _ _ _

lemma fill_prescribed {U : SSet.{v}} (j : U ⟶ S) : fill K i hK b a ha (j ≫ b) = j ≫ a := by
  rw [fill, Category.assoc, section_prescribed]

abbrev family : SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ⊗ L ⟶ K :=
  uncurry (fill K i hK b a ha boundary)

lemma family_boundary : (SSet.horn (n + 1) i).ι ▷ L ≫ family K i hK b a ha boundary =
    uncurry boundary :=
  (uncurry_pre_app K (fill K i hK b a ha boundary) (SSet.horn (n + 1) i).ι).symm.trans
    (congrArg uncurry (fill_restriction K i hK b a ha boundary))

lemma family_naturality {U : SSet.{v}} (j : U ⟶ L) :
    family K i hK b a ha (j ≫ boundary) =
      SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ◁ j ≫ family K i hK b a ha boundary := by
  rw [family, fill_naturality, uncurry_natural_left]

lemma family_prescribed {U : SSet.{v}} (j : U ⟶ S) : family K i hK b a ha (j ≫ b) =
    SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ◁ j ≫ uncurry a := by
  rw [family, fill_prescribed, uncurry_natural_left]

end SerrePositivity.SimplicialModel.RelativeHornFillingOperation
