module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PresheafCoconeImageLegs

/-!
概要：指定前層余極限の実際の各脚の全余錐変換を、元の底脚と頂点脚へ厳密に制限する。
方針：同じ全錐の両制限を native 脚で評価し、元の全余錐の正方形へ代入する。
規約：元の全一単体を保持し、点での同型の自然性を仮定しない。
使われ方：非空有限錐の実際の像と標準全評価 Kan 錐の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
open SSet.Truncated.HomotopyCategory
variable {B C K : SSet.{u}}
  {r : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ PresheafInfinity C}
  (q : JoinCocone r) {p : K ⟶ C.op} (c : JoinCone p)
  (k : ((SSet.uliftFunctor.{u + 1, u}).obj K) _⦋0⦌)
local notation "q₀" => F1B.kanPostcomposeCocone
  (evaluateFunctorAt (JoinCone.vertex (JoinCone.ulift c))) q
local notation "q₁" => F1B.kanPostcomposeCocone
  (evaluateFunctorAt (NatTrans.app (CategoryTheory.Functor.map SSet.uliftFunctor p)
    (Opposite.op ⦋0⦌) k)) q

/-- 元の全余錐変換の底辺は、元の交換評価全錐の同じ native 脚。 -/
lemma presheafCoconeImageLeg_bottom :
    (coconeWholeEdgeBottom q₀ q₁ (presheafCoconeImageLeg q c k).toTruncated).edge =
      (F2.nativeConeLeg (mapJoinCone (internalHomFlipHomEquiv _ _ _ r)
        (JoinCone.ulift.{u, u + 1} c)) k).edge := by
  exact congrArg (fun d ↦ (F2.nativeConeLeg d k).edge)
    (presheafCoconeImageCone_restriction q c)

/-- 元の全余錐変換の頂点辺の各点評価は、実際の余極限頂点関手による同じ元の脚。 -/
lemma presheafCoconeImageLeg_top_at
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj B) _⦋0⦌) :
    (evaluateFunctorAt b).app (Opposite.op ⦋1⦌)
      (coconeWholeEdgeTop q₀ q₁ (presheafCoconeImageLeg q c k).toTruncated).edge =
        (F2.nativeConeLeg (mapJoinCone (presheafCoconeVertexFunctor q)
          (JoinCone.ulift.{u, u + 1} c)) k).edge := by
  let a := coconeRightApexVertex ((SSet.uliftFunctor.{u + 1, u}).obj B)
  let j : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _ := SSet.const a
  have he : (pre j).app SpaceInfinity.{u} ≫ evaluateFunctorAt b = evaluateFunctorAt a := by
    rw [evaluateFunctorAt_pre]
    change evaluateFunctorAt (PinchedHom.constant a 0) = evaluateFunctorAt a
    rw [pinchedConstant_zero]
  have h := congrArg (fun d ↦ (F2.nativeConeLeg d k).edge) (presheafCoconeImageCone_apex q c)
  calc
    _ = (evaluateFunctorAt a).app (Opposite.op ⦋1⦌)
        (F2.nativeConeLeg (presheafCoconeImageCone q c) k).edge :=
      congrArg (fun f ↦ f.app (Opposite.op ⦋1⦌)
        (F2.nativeConeLeg (presheafCoconeImageCone q c) k).edge) he
    _ = _ := h

/-- 元の実際の全錐の脚の底変換と頂点変換は、元の両評価余錐変換と可換。 -/
lemma presheafCoconeImageLeg_square :
    homMk (coconeWholeEdgeBottom q₀ q₁ (presheafCoconeImageLeg q c k).toTruncated).toTruncated ≫
      homMk (intervalMappingEdgeOfVertex (F2.coconeTransformationVertex q₁)).toTruncated =
    homMk (intervalMappingEdgeOfVertex (F2.coconeTransformationVertex q₀)).toTruncated ≫
      homMk (coconeWholeEdgeTop q₀ q₁ (presheafCoconeImageLeg q c k).toTruncated).toTruncated :=
  coconeWholeEdge_square q₀ q₁ (presheafCoconeImageLeg q c k).toTruncated

end SerrePositivity.InfinityCategories.HomotopyLimits
