module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.UniverseLift

/-!
# 小さい値の境界充填を単体的宇宙liftへ移す

## 概要
小さい値の境界充填を単体的宇宙liftへ移す。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
各次数のULiftの上げ下げを明示し、単体作用素との交換を確認する。
写像・充填またはホモトピーを同じ全パラメータのまま移送する。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0593][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0593
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Small boundary fillers across simplicial universes

This extends the existing universe-lift API. Finite boundary fillers in
the smaller universe supply fillers after lifting; no larger model
structure is needed.
-/

@[expose] public section
universe w v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers

abbrev obj (P : SSet.{v}) : SSet.{max w v} := SSet.uliftFunctor.{w, v}.obj P
abbrev map {P Q : SSet.{v}} (f : P ⟶ Q) : obj.{w} P ⟶ obj.{w} Q :=
  SSet.uliftFunctor.{w, v}.map f

def lower {P Q : SSet.{v}} (f : obj.{w} P ⟶ obj.{w} Q) : P ⟶ Q where
  app n := ↾fun x => (f.app n ⟨x⟩).down
  naturality {_ _} θ := by
    refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
    exact congrArg ULift.down (congrArg (fun h => h (ULift.up x)) (f.naturality θ))

lemma map_lower {P Q : SSet.{v}} (f : obj.{w} P ⟶ obj.{w} Q) : map (lower f) = f := rfl
lemma lower_map {P Q : SSet.{v}} (f : P ⟶ Q) : lower (map.{w} f) = f := rfl

@[reassoc]
lemma map_comp {P Q R : SSet.{v}} (f : P ⟶ Q) (g : Q ⟶ R) :
    map.{w} (f ≫ g) = map f ≫ map g := rfl

abbrev stdIso (d : ℕ) : obj.{w} (SSet.stdSimplex.{v}.obj (SimplexCategory.mk d)) ≅
    SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk d) := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIso (SimplexCategory.mk d)

@[reassoc]
lemma boundary_square (d : ℕ) :
    map.{w} (SSet.boundary.{v} d).ι ≫ (stdIso.{w, v} d).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.boundaryIso.{w, v} d).hom ≫ (SSet.boundary.{max w v} d).ι := rfl

/-- Existence of fillers for all finite boundaries, before choosing a model structure. -/
abbrev BoundaryFillers (P : SSet.{v}) : Prop := ∀ (d : ℕ)
  (b : (SSet.boundary.{v} d).toSSet ⟶ P),
  ∃ e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk d) ⟶ P, (SSet.boundary.{v} d).ι ≫ e = b

/-- 小さい値の境界充填を単体的宇宙liftへ移す。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
各次数のULiftの上げ下げを明示し、単体作用素との交換を確認する。
写像・充填またはホモトピーを同じ全パラメータのまま移送する。
-/
lemma boundaryFillers {P : SSet.{v}} (hp : BoundaryFillers P) : BoundaryFillers (obj.{w} P) := by
  intro d b
  obtain ⟨e, he⟩ := hp d (lower ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.boundaryIso.{w, v} d).hom ≫ b))
  refine ⟨(stdIso.{w, v} d).inv ≫ map e, ?_⟩
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.boundaryIso.{w, v} d).hom).mp
  calc
    _ = (map (SSet.boundary.{v} d).ι ≫ (stdIso.{w, v} d).hom) ≫
        (stdIso.{w, v} d).inv ≫ map e := by
      simpa only [Category.assoc] using
        congrArg (fun q => q ≫ (stdIso.{w, v} d).inv ≫ map e) (boundary_square.{w, v} d).symm
    _ = map ((SSet.boundary.{v} d).ι ≫ e) := by
      rw [Category.assoc, Iso.hom_inv_id_assoc, map_comp]
    _ = _ := by rw [he, map_lower]

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers
