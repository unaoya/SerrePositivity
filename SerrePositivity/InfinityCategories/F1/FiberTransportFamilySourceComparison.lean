module

public import SerrePositivity.InfinityCategories.F1.ParametrizedFiberTransportNaturality

/-!
概要：始点 fiber への任意の係数射を持つ輸送族と普遍輸送の比較。
方針：始点が恒等の輸送族を係数射で制限し、族全体の選択独立性を使う。
規約：比較は全パラメーター上の一つの関手同型。
使われ方：豊穣 Hom の fiber 比較を始点とする標準合成輸送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：任意の係数射を持つ輸送族は普遍輸送にその係数射を前合成した作用と同型。
方針：恒等係数の輸送族との比較を係数射で制限し、同じ初期条件の輸送を比較する。
規約：パラメーターは頂点や辺に制限しない。
使われ方：標準合成輸送から普遍輸送への全パラメーター付き比較。 -/
def FiberTransportFamily.mapIso_parametrizedSource {E B K L : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌} (f : K ⟶ vertexFiber p a)
    (γ : Δ[1] ⊗ L ⟶ B)
    (h₀ : prismEndpoint 0 L ≫ γ = SSet.const a)
    (h₁ : prismEndpoint 1 L ≫ γ = SSet.const b)
    (T : FiberTransportFamily (b := b) p f γ) :
    FunctorIso T.map (intervalMappingCurryOfEndpoints γ h₀ h₁ ≫
      parametrizedFiberTransport p a b ≫ (pre f).app (vertexFiber p b)) := by
  let U₀ := fiberTransportFamily p (𝟙 (vertexFiber p a)) γ h₀ h₁
  let U₁ := U₀.precomposeSource f
  let U : FiberTransportFamily (b := b) p f γ :=
    ⟨U₁.endpoint, U₁.prism, by simpa only [Category.comp_id] using U₁.start,
      U₁.finish, U₁.over_base⟩
  have e₁ := T.mapIso p f γ h₁ U
  change FunctorIso T.map U₁.map at e₁
  rw [FiberTransportFamily.precomposeSource_map] at e₁
  have e₀ := FunctorIso.postcomp (U₀.mapIso_parametrized p γ h₀ h₁)
    ((pre f).app (vertexFiber p b))
  exact e₁.trans (by simpa only [Category.assoc] using e₀)

end SerrePositivity.InfinityCategories
