module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedRelativeFiberCurry
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PrismFiberOutputLiftPointed
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionEndpointCoordinates

/-!
概要：同じ prism の終点を、pointed fiber の同型で直接元の小さい fiber の関手へ写す。
方針：底の終点が定値である等式を明示し、同じ延長の包含・終点制限・fiber curry を合成する。
規約：元の全 prism と指定類を保持。使われ方：新旧の fiber 出力の厳密な比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌)
local notation "a" => coherentNativeTriangleFiberParameters F b
local notation "m" => smallUnstraighteningSourceRestriction F
  (vertexFiberι (smallLeftUnstraighteningProjection F) b)
local notation "c" => Over.Hom.left m ≫ leftUnstraighteningProjection F
local notation "src" => coherentCospanFiberPointedSource F b
variable (q : (Δ[1] : SSet.{u + 1}) ⊗
    coherentNativeTriangleFiberParameters F b ⟶ SpaceInfinity.{u})
  (hq₀ : coherentCospanFiberPointedSource F b ≫ pointedSpaceProjection =
    prismEndpoint 0 (coherentNativeTriangleFiberParameters F b) ≫ q)
  (hq₁ : prismEndpoint 1 (coherentNativeTriangleFiberParameters F b) ≫ q =
    ((smallUnstraighteningSourceRestriction F
      (vertexFiberι (smallLeftUnstraighteningProjection F) b)).left ≫
        leftUnstraighteningProjection F) ≫ J)

include hq₁ in
/-- prism の終点の底は、元の最後の値の頂点に定値である。 -/
lemma coherentPrismDirectEndpoint_const :
    prismEndpoint 1 a ≫ q = SSet.const (J.app (Opposite.op ⦋0⦌) (ULift.up b)) := by
  rw [hq₁, smallFiberSourceRestriction_projection F b, SSet.const_comp]

/-- 元の全 prism の終点を、明示した pointed fiber の同型で直接評価する写像。 -/
def coherentPrismDirectFiberOutput :
    relativeFunctorExtensionSpace pointedSpaceProjection q (prismEndpoint 0 a) src hq₀ ⟶
      (ihom a).obj (coherentNativeTriangleFiberParameters J b) :=
  relativeFunctorExtensionSpaceι pointedSpaceProjection q (prismEndpoint 0 a) src hq₀ ≫
    relativeFunctorPre pointedSpaceProjection q (prismEndpoint 1 a) ≫
      pointedRelativeFiberCurry J b (prismEndpoint 1 a ≫ q)
        (coherentPrismDirectEndpoint_const F J b q hq₁)

/-- 直接評価も、元の同じ全 prism の終点の pointed 全族を厳密に回収する。 -/
lemma coherentPrismDirectFiberOutput_pointed :
    uncurry (coherentPrismDirectFiberOutput F J b q hq₀ hq₁) ≫
      coherentCospanFiberPointedSource J b =
      relativeFunctorUncurry
        (relativeFunctorExtensionSpaceι pointedSpaceProjection q (prismEndpoint 0 a) src hq₀ ≫
          relativeFunctorPre pointedSpaceProjection q (prismEndpoint 1 a)) := by
  unfold coherentPrismDirectFiberOutput
  rw [← Category.assoc, uncurry_natural_left, Category.assoc,
    pointedRelativeFiberCurry_pointed, ← relativeFunctorUncurry_naturality, Category.comp_id]

/-- 旧終点の後の出力も、元の同じ全 prism の終点の pointed 全族を回収する。 -/
lemma coherentPrismEndpointOutputLift_pointed :
    uncurry (relativeFunctorExtensionEndpoint pointedSpaceProjection q (prismEndpoint 0 a)
      src hq₀ (prismEndpoint 1 a) J c hq₁ ≫ coherentPrismFiberOutputLift F J b) ≫
      coherentCospanFiberPointedSource J b =
      relativeFunctorUncurry
        (relativeFunctorExtensionSpaceι pointedSpaceProjection q (prismEndpoint 0 a) src hq₀ ≫
          relativeFunctorPre pointedSpaceProjection q (prismEndpoint 1 a)) := by
  rw [uncurry_natural_left, Category.assoc, coherentPrismFiberOutputLift_pointed]
  have he := relativeFunctorUncurry_id_parameter (leftUnstraighteningProjection J) c
    (relativeFunctorExtensionEndpoint pointedSpaceProjection q (prismEndpoint 0 a) src hq₀
      (prismEndpoint 1 a) J c hq₁)
  exact (Category.assoc _ _ _).symm.trans ((congrArg
    (fun k => k ≫ pullback.fst pointedSpaceProjection J) he).trans
      (relativeFunctorExtensionEndpoint_uncurry_fst _ _ _ _ _ _ _ _ _))

/-- 新旧の fiber 出力は、全パラメータを保つ同じ単体的写像である。 -/
lemma coherentPrismDirectFiberOutput_eq :
    coherentPrismDirectFiberOutput F J b q hq₀ hq₁ =
      relativeFunctorExtensionEndpoint pointedSpaceProjection q (prismEndpoint 0 a)
        src hq₀ (prismEndpoint 1 a) J c hq₁ ≫ coherentPrismFiberOutputLift F J b := by
  apply uncurry_injective
  have : Mono (coherentCospanFiberPointedSource J b) := by
    rw [← coherentFiberPointedSourceIso_hom_ι J b]
    infer_instance
  apply (cancel_mono (coherentCospanFiberPointedSource J b)).1
  exact (coherentPrismDirectFiberOutput_pointed F J b q hq₀ hq₁).trans
    (coherentPrismEndpointOutputLift_pointed F J b q hq₀ hq₁).symm

end SerrePositivity.InfinityCategories.F2
