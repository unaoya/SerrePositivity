module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanNativeCommonFiberOutput

/-!
概要：共通長辺の直接 fiber 評価が、元の全三角形の実延長頂点を保つことを示す。
方針：出力写像の厳密な一致と、相対 curry の実頂点公式を合成する。
規約：端点の等式を同型の HEq から取り出さない。使われ方：指定 path の端点補正の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "a" => coherentNativeTriangleFiberParameters F b
local notation "c" => coherentCospanConePointwiseCone F X Y Z C b
local notation "s" => coherentCospanFiberPointedSource F b
local notation "hs" => coherentCospanFiberPointedSource_projection F X Y Z C b
local notation "el" => SSet.yonedaEquiv horn₂₂.ι₀₂
local notation "er" => SSet.yonedaEquiv horn₂₂.ι₁₂
local notation "Dl" => SSet.yonedaEquiv.symm (nativeConeTriangle c el)
local notation "Dr" => SSet.yonedaEquiv.symm (nativeConeTriangle c er)
local notation "q" => coherentCospanNativeLongBase F X Y Z C b
local notation "hq" => coherentCospanNativeLongBase_initial F X Y Z C b
local notation "M" => coherentCospanNativeCommonFiberOutput F X Y Z C b

/-- 左三角形の任意の実延長は、同じ面の終点 fiber 評価の関手頂点へ写る。 -/
lemma coherentCospanNativeCommonFiberOutput_left_vertex
    (W : (Δ[2] : SSet.{u + 1}) ⊗ a ⟶ PointedSpaceInfinity.{u})
    (hW : W ≫ pointedSpaceProjection = fst Δ[2] a ≫ Dl)
    (hWi : (scaffoldFirstVertex 2 ▷ a) ≫ W = snd Δ[0] a ≫ s) :
    (M).app _ (nativePointedTriangleLongBaseChangeTarget c s hs el q hq rfl W hW hWi) =
      functorVertex (pointedTriangleFaceSections Dl W hW 0 ≫
        coherentCospanNativeLeftTargetFiberEvaluation F X Y Z C b) := by
  let w := nativePointedTriangleExtensionVertex c s hs el W hW hWi
  have h := congrArg (fun f => f.app (Opposite.op ⦋0⦌) w)
    (coherentCospanNativeLeftFinalFiberOutput_eq_common F X Y Z C b)
  exact h.symm.trans (relativeTriangleFinalFiberOutput_vertex Z b Dl _ _ _ 0 _ W hW hWi)

/-- 右三角形も同じ共通出力写像で、元の面の終点評価の関手頂点を保持する。 -/
lemma coherentCospanNativeCommonFiberOutput_right_vertex
    (W : (Δ[2] : SSet.{u + 1}) ⊗ a ⟶ PointedSpaceInfinity.{u})
    (hW : W ≫ pointedSpaceProjection = fst Δ[2] a ≫ Dr)
    (hWi : (scaffoldFirstVertex 2 ▷ a) ≫ W = snd Δ[0] a ≫ s) :
    (M).app _ (nativePointedTriangleLongBaseChangeTarget c s hs er q hq
      (coherentCospanNativeLongBase_right F X Y Z C b) W hW hWi) =
      functorVertex (pointedTriangleFaceSections Dr W hW 0 ≫
        coherentCospanNativeRightTargetFiberEvaluation F X Y Z C b) := by
  let w := nativePointedTriangleExtensionVertex c s hs er W hW hWi
  have h := congrArg (fun f => f.app (Opposite.op ⦋0⦌) w)
    (coherentCospanNativeRightFinalFiberOutput_eq_common F X Y Z C b)
  exact h.symm.trans (relativeTriangleFinalFiberOutput_vertex Z b Dr _ _ _ 0 _ W hW hWi)

end SerrePositivity.InfinityCategories.F2
