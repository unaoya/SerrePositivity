module

public import SerrePositivity.InfinityCategories.F2.PrismDirectFiberOutput
public import SerrePositivity.InfinityCategories.F2.FunctorSpaceDown
public import SerrePositivity.InfinityCategories.F2.UniverseDownFunctorCancellation

/-!
概要：旧 prism の全出力関手を、同じ直接 fiber 評価と関手空間の下降へ厳密に同定する。
方針：出力表示の同型の往復を消し、新旧の単体的写像の厳密な一致を適用する。
規約：対象と全射を保持。使われ方：左右の指定比較の合成と端点補正の同時照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌)
local notation "pF" => smallLeftUnstraighteningProjection F
local notation "pJ" => smallLeftUnstraighteningProjection J
local notation "i" => vertexFiberι pF b
local notation "a" => coherentNativeTriangleFiberParameters F b
local notation "m" => smallUnstraighteningSourceRestriction F i
local notation "c" => Over.Hom.left m ≫ leftUnstraighteningProjection F
local notation "src" => coherentCospanFiberPointedSource F b
local notation "Q" => relativeFunctorBaseFiberHom pJ (i ≫ pF) b (vertexFiberι_comp pF b)

/-- 旧 prism 出力関手は、同じ直接 fiber 評価を下降した一つの関手である。 -/
lemma coherentPrismFiberFunctor_eq_direct
    (q : (Δ[1] : SSet.{u + 1}) ⊗ a ⟶ SpaceInfinity.{u})
    (hq₀ : src ≫ pointedSpaceProjection = prismEndpoint 0 a ≫ q)
    (hq₁ : prismEndpoint 1 a ≫ q = c ≫ J) :
    coherentPrismFiberFunctor F J b q hq₀ hq₁ =
      SSet.mapHomotopyCategory (coherentPrismDirectFiberOutput F J b q hq₀ hq₁) ⋙
        functorSpaceDown (vertexFiber pF b) (vertexFiber pJ b) := by
  let P := relativeFunctorExtensionEndpoint pointedSpaceProjection q (prismEndpoint 0 a)
    src hq₀ (prismEndpoint 1 a) J c hq₁
  have h := universeHomotopyDown_post_functor_iso_cancel
    (P ≫ coherentPrismEndpointShrink F J b) Q
    (uliftFunctorSpaceIso (vertexFiber pF b) (vertexFiber pJ b))
  rw [coherentPrismDirectFiberOutput_eq]
  change _ = SSet.mapHomotopyCategory (P ≫ coherentPrismFiberOutputLift F J b) ⋙ _
  unfold coherentPrismFiberOutputLift
  simpa only [coherentPrismFiberFunctor, P, Category.assoc, functorSpaceDown] using h

end SerrePositivity.InfinityCategories.F2
