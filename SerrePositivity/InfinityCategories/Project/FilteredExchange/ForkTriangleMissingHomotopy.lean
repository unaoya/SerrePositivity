module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.ForkHomotopyHorn

/-!
概要：指定二円柱を保持する充填三角形の欠けた辺から、実際の反転ホモトピーを読む。
方針：ホーンの二辺と欠けた辺の端点を照合する。
規約：充填三角形の欠けた辺そのものを全円柱として返す。
使われ方：指定部分円柱を厳密に保つ相対比較の反転。
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
  (U : SSet.Homotopy f₀ f₁) (V : SSet.Homotopy f₀ f₂)
  (F : (Δ[2] : SSet.{u}) ⊗ K ⟶ X)
  (hF : ((horn 2 0).ι ▷ K) ≫ F = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.forkHomotopyHorn U V)
include hF

/-- 概要：充填の第一辺は元の第一円柱。
方針：ホーンの第一辺へ制限する。規約：全円柱。使われ方：反転円柱の始点条件。 -/
lemma forkTriangleMissingHomotopy_first :
    (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ F = (β_ (Δ[1] : SSet.{u}) K).hom ≫ U.h := by
  have h := congrArg (fun r ↦ (horn₂₀.ι₀₁ ▷ K) ≫ r) hF
  rw [← comp_whiskerRight_assoc, horn.ι_ι, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.forkHomotopyHorn_first] at h
  exact h

/-- 概要：充填の第二辺は元の第二円柱。
方針：ホーンの第二辺へ制限する。規約：全円柱。使われ方：反転円柱の終点条件。 -/
lemma forkTriangleMissingHomotopy_last :
    (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ F = (β_ (Δ[1] : SSet.{u}) K).hom ≫ V.h := by
  have h := congrArg (fun r ↦ (horn₂₀.ι₀₂ ▷ K) ≫ r) hF
  rw [← comp_whiskerRight_assoc, horn.ι_ι, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.forkHomotopyHorn_last] at h
  exact h

/-- 概要：充填三角形の欠けた辺は元の始点から元の終点への実際のホモトピー。
方針：二辺の端点と欠けた辺の端点の一致を使う。
規約：欠けた辺の全円柱。使われ方：境界指定の比較円柱の反転。 -/
def forkTriangleMissingHomotopy : SSet.Homotopy f₁ f₂ where
  h := (β_ K (Δ[1] : SSet.{u})).hom ≫ (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ F
  h₀ := by
    have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ (stdSimplex.δ (0 : Fin 3) ▷ K) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ (stdSimplex.δ (2 : Fin 3) ▷ K) := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro x
      rfl
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ F = f₁
    rw [← Category.assoc, hp, Category.assoc, forkTriangleMissingHomotopy_first U V F hF]
    change SSet.ι₁ ≫ U.h = f₁
    exact U.h₁
  h₁ := by
    have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ (stdSimplex.δ (0 : Fin 3) ▷ K) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ (stdSimplex.δ (1 : Fin 3) ▷ K) := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro x
      rfl
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ F = f₂
    rw [← Category.assoc, hp, Category.assoc, forkTriangleMissingHomotopy_last U V F hF]
    change SSet.ι₁ ≫ V.h = f₂
    exact V.h₁
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end SerrePositivity.InfinityCategories.Project.FilteredExchange
