module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorPrismFamilyCurry
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorParameterizedPrismNaturality

/-!
概要：変換空間へ戻した族はパラメーター制限を厳密に保つ。
方針：区間模型と prism の評価の単射性で検査する。
規約：入力の prism の制限の等式を明示する。
使われ方：積の底上の変換の比較を族の関手同型へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：同じ制限の prism を与える curry は同じ変換の族となる。
方針：区間の uncurry とパラメーター付き prism の単射性を使う。
規約：底の小ささや充填性は不要。
使われ方：パラメーターの頂点での変換の族の回収。 -/
lemma coherentTransformationFamilyCurry_comp {B K L : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (i : L ⟶ K)
    (H : (Δ[1] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ SpaceInfinity.{u})
    (H' : (Δ[1] : SSet.{u + 1}) ⊗ (B ⊗ L) ⟶ SpaceInfinity.{u})
    (h₀ : prismEndpoint 0 (B ⊗ K) ≫ H = CartesianMonoidalCategory.fst B K ≫ F)
    (h₁ : prismEndpoint 1 (B ⊗ K) ≫ H = CartesianMonoidalCategory.fst B K ≫ G)
    (h₀' : prismEndpoint 0 (B ⊗ L) ≫ H' = CartesianMonoidalCategory.fst B L ≫ F)
    (h₁' : prismEndpoint 1 (B ⊗ L) ≫ H' = CartesianMonoidalCategory.fst B L ≫ G)
    (he : ((Δ[1] ⊗ B) ◁ i) ≫ ((α_ Δ[1] B K).hom ≫ H) =
      (α_ Δ[1] B L).hom ≫ H') :
    i ≫ coherentTransformationFamilyCurry F G H h₀ h₁ =
      coherentTransformationFamilyCurry F G H' h₀' h₁' := by
  apply intervalMappingUncurry_injective (functorVertex F) (functorVertex G)
  apply functorParameterizedPrism_injective
  rw [intervalMappingUncurry_precomp, functorParameterizedPrism_parameter,
    coherentTransformationFamilyCurry_prism, coherentTransformationFamilyCurry_prism]
  exact he

end SerrePositivity.InfinityCategories
