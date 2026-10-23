module

public import SerrePositivity.InfinityCategories.F1.Transport.DiagonalFiberTransport
public import SerrePositivity.InfinityCategories.F1.Transport.FiberTransportSquare

/-!
概要：底と全空間の可換四角形に沿う対角輸送の自然性。
方針：元の普遍輸送の prism を全空間の射で移し、標的の普遍輸送と比較する。
規約：始点と辺は同じ任意のパラメーターで動く。係数の逆同値は選ばない。
使われ方：反対 Kan nerve 上の合成の比較を実際の pointed-space 射影へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 任意の輸送族を動く係数と辺へ同時に制限すると、対角輸送と関手同型。 -/
def FiberTransportFamily.diagonalIso {P E B K L : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
    (f : K ⟶ vertexFiber p a) (γ : Δ[1] ⊗ L ⟶ B)
    (h₀ : prismEndpoint 0 L ≫ γ = SSet.const a)
    (h₁ : prismEndpoint 1 L ≫ γ = SSet.const b)
    (T : FiberTransportFamily (b := b) p f γ) (x : P ⟶ K) (y : P ⟶ L) :
    FunctorIso (lift x y ≫ T.endpoint)
      (diagonalFiberTransport p (x ≫ f)
        (y ≫ intervalMappingCurryOfEndpoints γ h₀ h₁)) := by
  let d := lift x y
  let H := (Δ[1] ◁ d) ≫ T.prism
  let v := y ≫ intervalMappingCurryOfEndpoints γ h₀ h₁
  have H₀ : prismEndpoint 0 P ≫ H = (x ≫ f) ≫ vertexFiberι p a := by
    dsimp only [H]
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, T.start,
      ← Category.assoc, ← Category.assoc, lift_fst, Category.assoc]
  have H₁ : prismEndpoint 1 P ≫ H = (lift x y ≫ T.endpoint) ≫ vertexFiberι p b := by
    dsimp only [H]
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, T.finish]
    rfl
  have Hp : H ≫ p = intervalMappingUncurry v := by
    dsimp only [H]
    rw [Category.assoc, T.over_base, ← whiskerLeft_comp_assoc, lift_snd]
    dsimp only [v]
    rw [intervalMappingUncurry_precomp, intervalMappingUncurry_curryOfEndpoints]
  have e := leftFibrationPrism_diagonalTransportIso p (x ≫ f) (lift x y ≫ T.endpoint)
    (intervalMappingUncurry v) (intervalMappingUncurry_zero v)
    (intervalMappingUncurry_one v) H H₀ H₁ Hp
  have hv : intervalMappingCurryOfEndpoints (intervalMappingUncurry v)
      (intervalMappingUncurry_zero v) (intervalMappingUncurry_one v) = v := by
    apply intervalMappingUncurry_injective _ _
    exact intervalMappingUncurry_curryOfEndpoints _ _ _
  rw [hv] at e
  exact e

/-- 可換四角形は、動く始点と辺の対角輸送を全パラメーターで保つ。 -/
def diagonalFiberTransport_squareIso {P E B F D : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ D) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (g : B ⟶ D) (h : f ≫ q = p ≫ g)
    {a b : B _⦋0⦌} (x : P ⟶ vertexFiber p a) (c : P ⟶ intervalMappingSpace a b) :
    FunctorIso
      (diagonalFiberTransport p x c ≫ transportSquareFiberMap p q f g h b)
      (diagonalFiberTransport q (x ≫ transportSquareFiberMap p q f g h a)
        (c ≫ intervalMappingPost g a b)) := by
  let T := parametrizedFiberTransportFamily p a b
  let d := lift x c
  let H := (Δ[1] ◁ d) ≫ T.prism ≫ f
  let v := c ≫ intervalMappingPost g a b
  have H₀ : prismEndpoint 0 P ≫ H =
      (x ≫ transportSquareFiberMap p q f g h a) ≫ vertexFiberι q (g.app _ a) := by
    dsimp only [H]
    rw [← Category.assoc, ← Category.assoc, prismEndpoint_naturality,
      Category.assoc d _ _, T.start]
    simp only [Category.assoc, transportSquareFiberMap_ι]
    change (d ≫ fst _ _) ≫ vertexFiberι p a ≫ f = _
    rw [lift_fst]
  have H₁ : prismEndpoint 1 P ≫ H =
      (diagonalFiberTransport p x c ≫ transportSquareFiberMap p q f g h b) ≫
        vertexFiberι q (g.app _ b) := by
    dsimp only [H]
    rw [← Category.assoc, ← Category.assoc, prismEndpoint_naturality,
      Category.assoc d _ _, T.finish]
    rfl
  have Hp : H ≫ q = intervalMappingUncurry v := by
    dsimp only [H]
    rw [Category.assoc, Category.assoc, h, ← Category.assoc T.prism p g,
      T.over_base, Category.assoc,
      ← whiskerLeft_comp_assoc, lift_snd,
      ← Category.assoc (Δ[1] ◁ c) _ g, ← intervalMappingUncurry_precomp,
      Category.comp_id]
    exact (intervalMappingPost_uncurry g a b c).symm
  have e := leftFibrationPrism_diagonalTransportIso q
    (x ≫ transportSquareFiberMap p q f g h a)
    (diagonalFiberTransport p x c ≫ transportSquareFiberMap p q f g h b)
    (intervalMappingUncurry v) (intervalMappingUncurry_zero v)
    (intervalMappingUncurry_one v) H H₀ H₁ Hp
  have hv : intervalMappingCurryOfEndpoints (intervalMappingUncurry v)
      (intervalMappingUncurry_zero v) (intervalMappingUncurry_one v) = v := by
    apply intervalMappingUncurry_injective _ _
    exact intervalMappingUncurry_curryOfEndpoints _ _ _
  rw [hv] at e
  exact e

end SerrePositivity.InfinityCategories
