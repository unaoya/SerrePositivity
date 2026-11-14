module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.ComposableHomotopyHorn
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.HomotopyTriangleEdges

/-!
概要：指定二円柱を保持する充填三角形の長辺から、実際の合成ホモトピーを読む。
方針：ホーンの二辺と長辺の端点を照合する。
規約：充填三角形の長辺そのものを全円柱として返す。
使われ方：指定部分円柱を厳密に保つ相対比較の合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {K X : SSet.{u}} {f₀ f₁ f₂ : K ⟶ X}
  (U : SSet.Homotopy f₀ f₁) (V : SSet.Homotopy f₁ f₂)
  (F : (Δ[2] : SSet.{u}) ⊗ K ⟶ X)
  (hF : ((horn 2 1).ι ▷ K) ≫ F = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.composableHomotopyHorn U V)
include hF

/-- 概要：充填の第一辺は元の第一円柱。
方針：ホーンの第一辺へ制限する。規約：全円柱。使われ方：合成円柱の始点条件。 -/
lemma homotopyTriangleComposite_first :
    (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ F = (β_ (Δ[1] : SSet.{u}) K).hom ≫ U.h := by
  have h := congrArg (fun r ↦ (horn₂₁.ι₀₁ ▷ K) ≫ r) hF
  rw [← comp_whiskerRight_assoc, horn.ι_ι, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.composableHomotopyHorn_first] at h
  exact h

/-- 概要：充填の第二辺は元の第二円柱。
方針：ホーンの第二辺へ制限する。規約：全円柱。使われ方：合成円柱の終点条件。 -/
lemma homotopyTriangleComposite_last :
    (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ F = (β_ (Δ[1] : SSet.{u}) K).hom ≫ V.h := by
  have h := congrArg (fun r ↦ (horn₂₁.ι₁₂ ▷ K) ≫ r) hF
  rw [← comp_whiskerRight_assoc, horn.ι_ι, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.composableHomotopyHorn_last] at h
  exact h

/-- 概要：充填三角形の長辺は元の始点から元の終点への実際のホモトピー。
方針：二辺の端点と長辺の端点の一致を使う。
規約：長辺の全円柱。使われ方：境界指定の比較円柱の合成。 -/
def homotopyTriangleComposite : SSet.Homotopy f₀ f₂ where
  h := (β_ K (Δ[1] : SSet.{u})).hom ≫ (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ F
  h₀ := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ F = f₀
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.homotopyTriangle_long_zero_prism, Category.assoc,
      homotopyTriangleComposite_first U V F hF]
    change SSet.ι₀ ≫ U.h = f₀
    exact U.h₀
  h₁ := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ F = f₂
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.homotopyTriangle_long_one_prism, Category.assoc,
      homotopyTriangleComposite_last U V F hF]
    change SSet.ι₁ ≫ V.h = f₂
    exact V.h₁
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end SerrePositivity.InfinityCategories.Project.FilteredExchange
