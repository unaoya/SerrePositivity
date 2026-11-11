module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.ComposableHomotopyHorn
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativeHornTensorExtension

/-!
概要：二つの指定円柱の合成三角形を、指定部分三角形を全体で固定して充填する。
方針：二次内ホーンと指定部分複体の積の和の anodyne 性を使う。
規約：元の二円柱と指定部分三角形を厳密に保持する。
使われ方：相対比較円柱を指定境界輸送に一致させた合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：元の二円柱と指定部分三角形の全単体を同時に保つ充填が存在する。
方針：共通部分で貼り、anodyne な積の和に沿って Kan 標的へ延長する。
規約：有限性は不要。使われ方：指定境界付きの実際のホモトピー合成。 -/
lemma exists_relativeHomotopyTriangle {K X : SSet.{u}} [KanComplex X]
    (A : K.Subcomplex) {f₀ f₁ f₂ : K ⟶ X}
    (U : SSet.Homotopy f₀ f₁) (V : SSet.Homotopy f₁ f₂)
    (b : (Δ[2] : SSet.{u}) ⊗ (A : SSet.{u}) ⟶ X)
    (hb₀ : (stdSimplex.δ (2 : Fin 3) ▷ (A : SSet.{u})) ≫ b =
      ((Δ[1] : SSet.{u}) ◁ A.ι) ≫ (β_ (Δ[1] : SSet.{u}) K).hom ≫ U.h)
    (hb₁ : (stdSimplex.δ (0 : Fin 3) ▷ (A : SSet.{u})) ≫ b =
      ((Δ[1] : SSet.{u}) ◁ A.ι) ≫ (β_ (Δ[1] : SSet.{u}) K).hom ≫ V.h) :
    ∃ F : (Δ[2] : SSet.{u}) ⊗ K ⟶ X,
      ((horn 2 1).ι ▷ K) ≫ F = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.composableHomotopyHorn U V ∧
      ((Δ[2] : SSet.{u}) ◁ A.ι) ≫ F = b := by
  have hw : ((horn 2 1).ι ▷ (A : SSet.{u})) ≫ b =
      ((horn 2 1 : SSet.{u}) ◁ A.ι) ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.composableHomotopyHorn U V := by
    apply (horn₂₁.isPushout.map (tensorRight (A : SSet.{u}))).hom_ext
    · change (horn₂₁.ι₀₁ ▷ (A : SSet.{u})) ≫
        (((horn 2 1).ι ▷ (A : SSet.{u})) ≫ b) = _
      rw [← comp_whiskerRight_assoc, horn.ι_ι]
      change (stdSimplex.δ (2 : Fin 3) ▷ (A : SSet.{u})) ≫ b =
        ((Δ[1] : SSet.{u}) ◁ A.ι) ≫ (horn₂₁.ι₀₁ ▷ K) ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.composableHomotopyHorn U V
      rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.composableHomotopyHorn_first]
      exact hb₀
    · change (horn₂₁.ι₁₂ ▷ (A : SSet.{u})) ≫
        (((horn 2 1).ι ▷ (A : SSet.{u})) ≫ b) = _
      rw [← comp_whiskerRight_assoc, horn.ι_ι]
      change (stdSimplex.δ (0 : Fin 3) ▷ (A : SSet.{u})) ≫ b =
        ((Δ[1] : SSet.{u}) ◁ A.ι) ≫ (horn₂₁.ι₁₂ ▷ K) ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.composableHomotopyHorn U V
      rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.composableHomotopyHorn_last]
      exact hb₁
  exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.exists_relativeHornTensorExtension A (1 : Fin 3)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.composableHomotopyHorn U V) b hw

end SerrePositivity.InfinityCategories.Project.FilteredExchange
