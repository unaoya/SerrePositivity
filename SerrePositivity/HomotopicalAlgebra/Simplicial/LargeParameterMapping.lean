module
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

public import SerrePositivity.HomotopicalAlgebra.Simplicial.LargeParameterHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing

/-!
# 大きいパラメータを持つ写像空間で互換な全面を充填する

## 概要
大きいパラメータを持つ写像空間で互換な全面を充填する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
テンソルと内部Homの随伴で族を転置し、対応する境界の等式を比較する。
転置の単射性と自然性により、元の全パラメータ族の等式へ戻す。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0443][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0443
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Boundary fillers for whole large-parameter mapping spaces

Every dimension is filled at once over the entire parameter object. The
uncurried extension retains the prescribed boundary, including any
previously selected global homotopies encoded there. No model structure
in the larger universe is needed.
-/

@[expose] public section
universe r w v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.LargeParameterMapping

instance boundaryMono (K : SSet.{r}) (d : ℕ) : Mono (K ◁ (SSet.boundary.{r} d).ι) := by
  have : ∀ n, Mono ((K ◁ (SSet.boundary.{r} d).ι).app n) := fun n =>
    (CategoryTheory.mono_iff_injective _).mpr (fun x y h => by
      change (x.1, x.2.val) = (y.1, y.2.val) at h
      apply Prod.ext
      · exact congrArg
          (fun z : K.obj n × (SSet.stdSimplex.{r}.obj (SimplexCategory.mk d)).obj n => z.1) h
      · apply Subtype.ext
        exact congrArg
          (fun z : K.obj n × (SSet.stdSimplex.{r}.obj (SimplexCategory.mk d)).obj n => z.2) h)
  exact NatTrans.mono_of_mono_app _

variable {P : SSet.{v}} (hp : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.BoundaryFillers P) (K : SSet.{max w v})

def fill (d : ℕ)
    (b : (SSet.boundary.{max w v} d).toSSet ⟶ (ihom K).obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P)) :
    SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk d) ⟶
      (ihom K).obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P) :=
  curry (LargeParameterExtension.extend hp (K ◁ (SSet.boundary.{max w v} d).ι) (uncurry b))

lemma fill_boundary (d : ℕ)
    (b : (SSet.boundary.{max w v} d).toSSet ⟶ (ihom K).obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P)) :
    (SSet.boundary.{max w v} d).ι ≫ fill hp K d b = b := by
  apply uncurry_injective
  rw [uncurry_natural_left, fill, uncurry_curry, LargeParameterExtension.extend_initial]

include hp in
/-- Boundary data in the mapping space retain all maps on the whole parameter K. -/
lemma fillers : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.BoundaryFillers ((ihom K).obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P)) :=
  fun d b => ⟨fill hp K d b, fill_boundary hp K d b⟩

/- 旧宣言の技術注記：
Fill a compatible collection of already specified global faces in any dimension ≥ 2.
-/
/-- 大きいパラメータを持つ写像空間で互換な全面を充填する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
テンソルと内部Homの随伴で族を転置し、対応する境界の等式を比較する。
転置の単射性と自然性により、元の全パラメータ族の等式へ戻す。
-/
def fillFaces {n : ℕ}
    (f : Fin (n + 3) → (SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk (n + 1)) ⟶
      (ihom K).obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P))) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.StandardCompatible f) :
    SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk (n + 2)) ⟶
      (ihom K).obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P) :=
  fill hp K (n + 2) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.standardDesc f hf)

lemma fillFaces_face {n : ℕ}
    (f : Fin (n + 3) → (SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk (n + 1)) ⟶
      (ihom K).obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P))) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.StandardCompatible f)
    (k : Fin (n + 3)) :
    SSet.stdSimplex.δ k ≫ fillFaces hp K f hf = f k := by
  rw [← SSet.boundary.ι_ι, Category.assoc, fillFaces, fill_boundary,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.standardDesc_fac]

/-- The exact prescribed face is retained as a map on K, before currying. -/
lemma fillFaces_uncurry_face {n : ℕ}
    (f : Fin (n + 3) → (SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk (n + 1)) ⟶
      (ihom K).obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P))) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.StandardCompatible f)
    (k : Fin (n + 3)) :
    K ◁ SSet.stdSimplex.δ k ≫ uncurry (fillFaces hp K f hf) = uncurry (f k) := by
  rw [← uncurry_natural_left, fillFaces_face]

end SerrePositivity.SimplicialModel.LargeParameterMapping
