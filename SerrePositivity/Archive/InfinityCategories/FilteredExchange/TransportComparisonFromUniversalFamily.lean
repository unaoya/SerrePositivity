module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ParametrizedFiberTransportNaturality

/-!
概要：元の全区間輸送族を変数として、同じ直接比較と実標的比較の値を照合する。
方針：元の二証拠・区間制限を保持し、全作用の表示変更を一般の輸送族上で除去する。
規約：新しい普遍輸送を選ばない。使われ方：元の具体的普遍輸送への適用を分離する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B L : SSet.{u}} (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
  (γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B)
  (h₁ : prismEndpoint 1 L ≫ γ = SSet.const b)
  (T : FiberTransportFamily (b := b) p (𝟙 (vertexFiber p a)) γ)
  (S : FiberTransportFamily (b := b) p (𝟙 (vertexFiber p a))
    (intervalMappingUncurry (𝟙 (intervalMappingSpace a b))))
  (k : L ⟶ intervalMappingSpace a b)
  (he : (Δ[1] ◁ k) ≫ intervalMappingUncurry (𝟙 (intervalMappingSpace a b)) = γ)

/-- 元の全区間輸送族への直接比較を、同じ実標的証拠で構成する一般の表示。 -/
def transportComparisonFromUniversalFamily : FunctorIso T.map (k ≫ S.map) := by
  let U₀ := S.precomp k
  let U : FiberTransportFamily (b := b) p (𝟙 (vertexFiber p a)) γ :=
    ⟨U₀.endpoint, U₀.prism, U₀.start, U₀.finish, by rw [U₀.over_base, he]⟩
  have e := T.mapIso p (𝟙 _) γ h₁ U
  change FunctorIso T.map U₀.map at e
  rw [FiberTransportFamily.precomp_map] at e
  exact e

/-- 同じ一般の直接比較は、同じ実標的との全作用比較の指定値を保つ。 -/
lemma transportComparisonFromUniversalFamily_heq_raw :
    HEq (transportComparisonFromUniversalFamily p γ h₁ T S k he)
      (let U₀ := S.precomp k
       let U : FiberTransportFamily (b := b) p (𝟙 (vertexFiber p a)) γ :=
         ⟨U₀.endpoint, U₀.prism, U₀.start, U₀.finish, by rw [U₀.over_base, he]⟩
       T.mapIso p (𝟙 _) γ h₁ U) := by
  change HEq (Eq.mp _ _) _
  have hcast {α β : Sort (u + 1)} (h : α = β) (z : α) : HEq (Eq.mp h z) z := by
    cases h
    rfl
  exact hcast _ _

end SerrePositivity.InfinityCategories.F2
