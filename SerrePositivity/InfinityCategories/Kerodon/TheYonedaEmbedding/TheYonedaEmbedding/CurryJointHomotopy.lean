module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy

/-!
概要：二変数の図式間の同じ自然変換を、第二変数から関手圏への自然変換へ curry する。
方針：円柱の結合子を入れて curry し、両端を uncurry で検査する。
規約：元の全円柱をそのまま用いる。各頂点での選択はしない。
使われ方：密度の共同 Hom の変換を、元の Yoneda 図式の全余錐へ戻す。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 同じ全二変数の円柱を curry した自然変換。 -/
def curryJointHomotopy {A B X : SSet.{u}} {f g : A ⊗ B ⟶ X}
    (H : SSet.Homotopy f g) : SSet.Homotopy (curry f) (curry g) where
  h := curry ((α_ A B (Δ[1] : SSet.{u})).inv ≫ H.h)
  h₀ := by
    change SSet.ι₀ ≫ curry ((α_ A B (Δ[1] : SSet.{u})).inv ≫ H.h) = curry f
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, uncurry_curry, ← Category.assoc]
    have he : (A ◁ (SSet.ι₀ : B ⟶ B ⊗ (Δ[1] : SSet.{u}))) ≫
        (α_ A B (Δ[1] : SSet.{u})).inv = SSet.ι₀ := rfl
    rw [he, H.h₀]
  h₁ := by
    change SSet.ι₁ ≫ curry ((α_ A B (Δ[1] : SSet.{u})).inv ≫ H.h) = curry g
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, uncurry_curry, ← Category.assoc]
    have he : (A ◁ (SSet.ι₁ : B ⟶ B ⊗ (Δ[1] : SSet.{u}))) ≫
        (α_ A B (Δ[1] : SSet.{u})).inv = SSet.ι₁ := rfl
    rw [he, H.h₁]
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
