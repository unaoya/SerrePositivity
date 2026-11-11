module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionFiberEndpointComposition

/-!
概要：同じ元の全区間族に沿う指定輸送の比較は、中間の選択を厳密に消去できる。
方針：既存の endpointIso を、同じ可縮な全延長空間の終点比較の合成則へ戻す。
規約：元の三輸送の prism と全係数を保持。使われ方：下側輸送因子の三角形整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の三つの全輸送の指定比較は、同じ直接比較へ厳密に合成する。 -/
lemma fiberTransportFamily_endpointIso_trans {E B K L : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌} (f : K ⟶ vertexFiber p a)
    (γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B)
    (h₁ : prismEndpoint 1 L ≫ γ = SSet.const b)
    (T U V : FiberTransportFamily (b := b) p f γ) :
    T.endpointIso p f γ h₁ U ≪≫ U.endpointIso p f γ h₁ V = T.endpointIso p f γ h₁ V := by
  unfold FiberTransportFamily.endpointIso
  apply relativeExtensionFiberEndpoint_witnessIso_trans

end SerrePositivity.InfinityCategories.F2
