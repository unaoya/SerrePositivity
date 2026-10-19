module

public import SerrePositivity.InfinityCategories.F1.TransportPrismLiftEvaluation
public import SerrePositivity.InfinityCategories.F1.PointedSpaceParametrizedEquivalence

/-!
概要：始点の同値を固定した全 lift prism の終点評価の同値性。
方針：全 lift の空間の射影と標準輸送の作用の同値性を関手同型で合成する。
規約：終点評価は全ての高次 lift を含む空間上の射。
使われ方：Kerodon Lemma 5.6.9.1 の固定始点比較と境界制限の中間段階。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：パラメーターが quasicategory なら全 lift prism の空間も quasicategory。
方針：trivial Kan fibration の射影の内ホーン充填を使う。
規約：係数 K や底 B の quasicategory 性は要求しない。
使われ方：終点評価と標準輸送の同値性の関手同型による比較。 -/
instance FiberTransportFamily.liftSpace_quasicategory {E B K L : SSet.{u}} {p : E ⟶ B}
    [LeftFibration p] [Quasicategory L] {a b : B _⦋0⦌}
    {f : K ⟶ vertexFiber p a} {γ : Δ[1] ⊗ L ⟶ B}
    (T : FiberTransportFamily (b := b) p f γ) : Quasicategory T.liftSpace :=
  quasicategory_of_innerFibration T.liftSpaceProjection

/-- 概要：選択済み輸送の作用が同値なら全 lift prism の終点評価も同値。
方針：パラメーター射影の trivial Kan fibration 性と終点評価の関手同型を使う。
規約：各 lift の頂点だけでなく空間全体についての同値性。
使われ方：普遍輸送の同値性から境界制限の中間空間の同値性を得る。 -/
lemma FiberTransportFamily.liftSpaceEndpoint_isQCatEquivalence {E B K L : SSet.{u}}
    {p : E ⟶ B} [LeftFibration p] [Quasicategory L] {a b : B _⦋0⦌}
    {f : K ⟶ vertexFiber p a} {γ : Δ[1] ⊗ L ⟶ B}
    (T : FiberTransportFamily (b := b) p f γ)
    (h₁ : prismEndpoint 1 L ≫ γ = SSet.const b) (hT : IsQCatEquivalence T.map) :
    IsQCatEquivalence (T.liftSpaceTransportFamily h₁).map :=
  ((isQCatEquivalence_of_trivialKanFibration T.liftSpaceProjection).comp hT).ofFunctorIso
    (T.liftSpaceEndpointIso h₁).symm

/-- 概要：始点の係数比較と区間パラメーター比較が同値なら pointed-space 輸送族の作用は同値。
方針：任意の係数の輸送族の普遍比較で、三つの同値の合成へ移す。
規約：T は選択済みの標準族である必要がない。
使われ方：固定した始点の同値に対する全 lift prism の終点比較。 -/
lemma pointedTransportFamily_map_isQCatEquivalence {K L : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory L] {s t : SpaceInfinity.{u} _⦋0⦌}
    (f : K ⟶ vertexFiber pointedSpaceProjection s) (hf : IsQCatEquivalence f)
    (γ : Δ[1] ⊗ L ⟶ SpaceInfinity.{u})
    (h₀ : prismEndpoint 0 L ≫ γ = SSet.const s)
    (h₁ : prismEndpoint 1 L ≫ γ = SSet.const t)
    (hγ : IsQCatEquivalence (intervalMappingCurryOfEndpoints γ h₀ h₁))
    (T : FiberTransportFamily (b := t) pointedSpaceProjection f γ) :
    IsQCatEquivalence T.map := by
  have h := (hγ.comp (parametrizedPointedSpaceTransport_isQCatEquivalence s t)).comp
    (hf.precompose (vertexFiber pointedSpaceProjection t))
  exact h.ofFunctorIso (T.mapIso_parametrizedSource pointedSpaceProjection f γ h₀ h₁).symm

/-- 概要：始点の同値を固定した pointed-space の全 lift prism の終点評価は同値。
方針：標準輸送の作用の同値性を lift 空間の射影と終点比較で移す。
規約：底の区間族も写像空間全体を表す同値を仮定する。
使われ方：Kerodon Lemma 5.6.9.1 の始点比較を固定した評価写像。 -/
lemma pointedPrismLiftEndpoint_isQCatEquivalence {K L : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory L] {s t : SpaceInfinity.{u} _⦋0⦌}
    (f : K ⟶ vertexFiber pointedSpaceProjection s) (hf : IsQCatEquivalence f)
    (γ : Δ[1] ⊗ L ⟶ SpaceInfinity.{u})
    (h₀ : prismEndpoint 0 L ≫ γ = SSet.const s)
    (h₁ : prismEndpoint 1 L ≫ γ = SSet.const t)
    (hγ : IsQCatEquivalence (intervalMappingCurryOfEndpoints γ h₀ h₁)) :
    IsQCatEquivalence
      ((fiberTransportFamily pointedSpaceProjection f γ h₀ h₁).liftSpaceTransportFamily h₁).map :=
  FiberTransportFamily.liftSpaceEndpoint_isQCatEquivalence _ h₁
    (pointedTransportFamily_map_isQCatEquivalence f hf γ h₀ h₁ hγ _)

/-- 概要：普遍的な区間族に対し始点の同値を固定した全 lift prism の終点評価は同値。
方針：普遍区間族の curry が恒等射であることを使う。
規約：s,t は任意の実際の空間の頂点。
使われ方：区間上の表現の境界制限へ適用する固定始点の評価。 -/
lemma pointedUniversalPrismLiftEndpoint_isQCatEquivalence {K : SSet.{u + 1}}
    [Quasicategory K] (s t : SpaceInfinity.{u} _⦋0⦌)
    (f : K ⟶ vertexFiber pointedSpaceProjection s) (hf : IsQCatEquivalence f) :
    IsQCatEquivalence ((fiberTransportFamily pointedSpaceProjection f
      (intervalMappingUncurry (𝟙 (intervalMappingSpace s t)))
      (intervalMappingUncurry_zero _) (intervalMappingUncurry_one _)).liftSpaceTransportFamily
        (intervalMappingUncurry_one _)).map := by
  apply pointedPrismLiftEndpoint_isQCatEquivalence f hf
  have h : intervalMappingCurryOfEndpoints
      (intervalMappingUncurry (𝟙 (intervalMappingSpace s t)))
      (intervalMappingUncurry_zero _) (intervalMappingUncurry_one _) =
      𝟙 (intervalMappingSpace s t) := by
    apply intervalMappingUncurry_injective s t
    exact intervalMappingUncurry_curryOfEndpoints _ _ _
  rw [h]
  exact (QCatEquivalence.refl _).isQCatEquivalence

end SerrePositivity.InfinityCategories
