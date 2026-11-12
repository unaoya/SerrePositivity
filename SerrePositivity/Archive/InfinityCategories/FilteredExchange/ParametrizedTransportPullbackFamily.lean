module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DiagonalUniversalPrism
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ParametrizedFiberTransportNaturality

/-!
概要：元の全区間普遍輸送族を、元の指定区間族へ引き戻した同じ標的証拠を公開する。
方針：元の全区間輸送の制限を、元の底の区間の表示へ戻す。
規約：普遍輸送を再選択しない。使われ方：指定一点区間の比較の実第二 prism の回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B L : SSet.{u}} (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
  (γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B)
  (h₀ : prismEndpoint 0 L ≫ γ = SSet.const a)
  (h₁ : prismEndpoint 1 L ≫ γ = SSet.const b)
local notation "k" => intervalMappingCurryOfEndpoints γ h₀ h₁

/-- 元の直接比較に用いる、全区間の普遍輸送を元の指定区間族へ制限した同じ標的証拠。 -/
def parametrizedTransportPullbackFamily :
    FiberTransportFamily (b := b) p (𝟙 (vertexFiber p a)) γ := by
  let U := (parametrizedFiberTransportFamily p a b).precomp k
  have he : (Δ[1] ◁ k) ≫ intervalMappingUncurry (𝟙 (intervalMappingSpace a b)) = γ := by
    rw [← intervalMappingUncurry_precomp, Category.comp_id]
    exact intervalMappingUncurry_curryOfEndpoints γ h₀ h₁
  exact ⟨U.endpoint, U.prism, U.start, U.finish, by rw [U.over_base, he]⟩

/-- 元の標的証拠の全作用は、元の同じ区間族による普遍輸送の前合成。 -/
lemma parametrizedTransportPullbackFamily_map :
    (parametrizedTransportPullbackFamily p γ h₀ h₁).map =
      k ≫ parametrizedFiberTransport p a b :=
  (parametrizedFiberTransportFamily p a b).precomp_map k

/-- 元の標的証拠の実 prism は、元の全区間普遍 prism の同じ制限。 -/
lemma parametrizedTransportPullbackFamily_prism :
    (parametrizedTransportPullbackFamily p γ h₀ h₁).prism =
      (Δ[1] ◁ (vertexFiber p a ◁ k)) ≫ (parametrizedFiberTransportFamily p a b).prism := rfl

/-- 元の標的 prism の同じ対角制限は、同じ元の動く初期値と区間の実普遍 prism。 -/
lemma parametrizedTransportPullbackFamily_diagonal_prism {Q : SSet.{u}}
    (s : Q ⟶ vertexFiber p a) (v : Q ⟶ L) :
    (Δ[1] ◁ lift s v) ≫ (parametrizedTransportPullbackFamily p γ h₀ h₁).prism =
      diagonalUniversalPrism p s (v ≫ k) := by
  rw [parametrizedTransportPullbackFamily_prism, ← Category.assoc, ← whiskerLeft_comp]
  have hn : lift s v ≫ (vertexFiber p a ◁ k) = lift s (v ≫ k) := by
    apply SSet.hom_ext
    intro n
    rfl
  rw [hn]
  rfl

end SerrePositivity.InfinityCategories.F2
