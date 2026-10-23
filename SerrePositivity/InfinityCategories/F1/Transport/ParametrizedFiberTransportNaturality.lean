module

public import SerrePositivity.InfinityCategories.F1.Transport.ParametrizedFiberTransport
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingPostcompositionVertices

/-!
概要：任意の固定端点の辺の族による輸送と普遍的な輸送射の前合成の比較。
方針：普遍的な持ち上げを同じパラメーターに引き戻し、族全体の選択独立性を使う。
規約：頂点での比較の族ではなく一つの関手同型を構成する。
使われ方：Kerodon Lemma 5.6.9.1、unstraightening の写像空間比較の対象ごとの評価。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：任意の辺の族の輸送は普遍輸送のパラメーター変更と関手同型。
方針：底の族を区間写像空間へ curry し、普遍的な持ち上げを引き戻して比較する。
規約：始点 fiber への係数射は恒等。
使われ方：選択済みの具体的な比較と普遍輸送の接続。 -/
noncomputable def FiberTransportFamily.mapIso_parametrized
    {E B L : SSet.{u}} (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
    (γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B)
    (h₀ : prismEndpoint 0 L ≫ γ = SSet.const a)
    (h₁ : prismEndpoint 1 L ≫ γ = SSet.const b)
    (T : FiberTransportFamily (b := b) p (𝟙 (vertexFiber p a)) γ) :
    FunctorIso T.map
      (intervalMappingCurryOfEndpoints γ h₀ h₁ ≫ parametrizedFiberTransport p a b) := by
  let h := intervalMappingCurryOfEndpoints γ h₀ h₁
  let U₀ := (parametrizedFiberTransportFamily p a b).precomp h
  have he : (Δ[1] ◁ h) ≫ intervalMappingUncurry (𝟙 (intervalMappingSpace a b)) = γ := by
    rw [← intervalMappingUncurry_precomp, Category.comp_id]
    exact intervalMappingUncurry_curryOfEndpoints γ h₀ h₁
  let U : FiberTransportFamily (b := b) p (𝟙 (vertexFiber p a)) γ :=
    ⟨U₀.endpoint, U₀.prism, U₀.start, U₀.finish, by rw [U₀.over_base, he]⟩
  have e := T.mapIso p (𝟙 _) γ h₁ U
  change FunctorIso T.map U₀.map at e
  rw [FiberTransportFamily.precomp_map] at e
  exact e

/-- 概要：後合成で評価した底の族を持つ輸送は写像空間の後合成と普遍輸送の合成に同型。
方針：一般の族の比較を、区間写像空間の後合成の定義で同定する。
規約：全写像空間上の関手同型。
使われ方：coherent diagram の変換を対象で評価した fiber の輸送との比較。 -/
noncomputable def FiberTransportFamily.mapIso_postcompose
    {E B X : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (f : X ⟶ B) (a b : X _⦋0⦌)
    (T : FiberTransportFamily (b := f.app _ b) p (𝟙 (vertexFiber p (f.app _ a)))
      (intervalMappingUncurry (𝟙 (intervalMappingSpace a b)) ≫ f)) :
    FunctorIso T.map
      (intervalMappingPost f a b ≫ parametrizedFiberTransport p (f.app _ a) (f.app _ b)) :=
  T.mapIso_parametrized p _
    (by rw [← Category.assoc, intervalMappingUncurry_zero, SSet.const_comp])
    (by rw [← Category.assoc, intervalMappingUncurry_one, SSet.const_comp])

end SerrePositivity.InfinityCategories
