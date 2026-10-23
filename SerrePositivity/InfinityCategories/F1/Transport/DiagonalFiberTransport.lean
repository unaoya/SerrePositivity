module

public import SerrePositivity.InfinityCategories.F1.Transport.ParametrizedFiberTransport
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.RelativeExtensionFiberEndpoint
public import SerrePositivity.InfinityCategories.F1.Transport.PrismLiftSpace

/-!
概要：始点の点と底の辺が同じパラメーターで動く場合の、実際の fiber transport の評価。
方針：普遍輸送の係数と辺のパラメーターを対角に制限し、指定した prism と比較する。
規約：パラメーターは任意の単体集合。始点を一定と仮定しない。
使われ方：coherent 自然性の pointed 四角形の短辺の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 始点と辺を同じパラメーターで評価する、普遍 fiber transport の実際の終点。 -/
def diagonalFiberTransport {P E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
    {a b : B _⦋0⦌} (f : P ⟶ vertexFiber p a) (c : P ⟶ intervalMappingSpace a b) :
    P ⟶ vertexFiber p b :=
  lift f c ≫ (parametrizedFiberTransportFamily p a b).endpoint

/-- 対角上の輸送は、普遍輸送を動く始点で評価する射そのもの。 -/
lemma diagonalFiberTransport_evaluate {P E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
    {a b : B _⦋0⦌} (f : P ⟶ vertexFiber p a) (c : P ⟶ intervalMappingSpace a b) :
    diagonalFiberTransport p f c =
      lift f (c ≫ parametrizedFiberTransport p a b) ≫
        (ihom.ev (vertexFiber p a)).app (vertexFiber p b) := by
  let T := parametrizedFiberTransportFamily p a b
  have h : lift f (c ≫ curry T.endpoint) =
      lift f c ≫ (vertexFiber p a ◁ curry T.endpoint) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  change lift f c ≫ T.endpoint = lift f (c ≫ curry T.endpoint) ≫ _
  rw [h, Category.assoc, whiskerLeft_curry_ihom_ev_app]

/-- 任意の動く始点の prism の終点は、同じ底の辺の普遍輸送の対角評価と関手同型。 -/
def leftFibrationPrism_diagonalTransportIso {P E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
    (f : P ⟶ vertexFiber p a) (g : P ⟶ vertexFiber p b)
    (γ : (Δ[1] : SSet.{u}) ⊗ P ⟶ B)
    (h₀ : prismEndpoint 0 P ≫ γ = SSet.const a)
    (h₁ : prismEndpoint 1 P ≫ γ = SSet.const b)
    (H : (Δ[1] : SSet.{u}) ⊗ P ⟶ E)
    (H₀ : prismEndpoint 0 P ≫ H = f ≫ vertexFiberι p a)
    (H₁ : prismEndpoint 1 P ≫ H = g ≫ vertexFiberι p b)
    (Hp : H ≫ p = γ) :
    FunctorIso g (diagonalFiberTransport p f (intervalMappingCurryOfEndpoints γ h₀ h₁)) := by
  let c := intervalMappingCurryOfEndpoints γ h₀ h₁
  let T := parametrizedFiberTransportFamily p a b
  let d := lift f c
  let V := (Δ[1] ◁ d) ≫ T.prism
  have V₀ : prismEndpoint 0 P ≫ V = f ≫ vertexFiberι p a := by
    dsimp only [V]
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, T.start,
      ← Category.assoc, ← Category.assoc]
    change (d ≫ fst _ _) ≫ (𝟙 _ ≫ vertexFiberι p a) = _
    rw [lift_fst, Category.id_comp]
  have V₁ : prismEndpoint 1 P ≫ V = diagonalFiberTransport p f c ≫ vertexFiberι p b := by
    dsimp only [V, diagonalFiberTransport]
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, T.finish, Category.assoc]
  have Vp : V ≫ p = γ := by
    dsimp only [V]
    rw [Category.assoc, T.over_base, ← whiskerLeft_comp_assoc, lift_snd,
      ← intervalMappingUncurry_precomp, Category.comp_id]
    exact intervalMappingUncurry_curryOfEndpoints γ h₀ h₁
  let i := prismEndpoint 0 P
  let v := f ≫ vertexFiberι p a
  have hv : v ≫ p = i ≫ γ := by
    dsimp only [v, i]
    rw [Category.assoc, vertexFiberι_comp, SSet.comp_const, h₀]
  exact relativeExtensionFiberEndpoint_witnessIso p γ i (prismEndpoint_zero_leftAnodyne P)
    v hv (prismEndpoint 1 P) b h₁ H V Hp Vp H₀ V₀ g (diagonalFiberTransport p f c) H₁ V₁

end SerrePositivity.InfinityCategories
