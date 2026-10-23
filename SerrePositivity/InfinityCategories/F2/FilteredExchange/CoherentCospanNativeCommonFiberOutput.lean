module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanNativeFinalFiberImage
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanPrismFiberFunctor
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.TrianglePrismDirectFiberOutput

/-!
概要：左右の全三角形の最終 fiber 出力を、共通長辺空間からの一つの直接評価へ同定する。
方針：元の長辺制限と底だけの等式移送に、全三角形の終点評価の厳密な一致を適用する。
規約：対象・全指定類を保持。使われ方：共通長辺の指定 path と切断模型の指定 path の照合。
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
local notation "h₁" => coherentCospanPrismEndpoint_projection F X Y Z C b
local notation "Rl" => triangleLongPrismExtensionRestriction pointedSpaceProjection
  (fst Δ[2] a ≫ Dl) (snd Δ[0] a ≫ s) (nativePointedConeTriangle_initial c s hs el)
local notation "Rr" => triangleLongPrismExtensionRestriction pointedSpaceProjection
  (fst Δ[2] a ≫ Dr) (snd Δ[0] a ≫ s) (nativePointedConeTriangle_initial c s hs er)

/-- 共通長辺空間の終点を、同じ元の小さい fiber 間の関手空間へ直接評価する写像。 -/
def coherentCospanNativeCommonFiberOutput := coherentPrismDirectFiberOutput F Z b q hq h₁

/-- 左の最終 fiber 出力は、長辺制限・共通の底移送・同じ直接評価の合成。 -/
lemma coherentCospanNativeLeftFinalFiberOutput_eq_common :
    coherentCospanNativeLeftFinalFiberOutput F X Y Z C b =
      Rl ≫ (coherentCospanNativeLeftLongBaseIso F X Y Z C b).hom ≫
        coherentCospanNativeCommonFiberOutput F X Y Z C b := by
  exact relativeTriangleFinalFiberOutput_eq_prism F Z b Dl
    (nativePointedConeTriangle_initial c s hs el) q hq h₁ rfl _

/-- 右も元の底の等式のみを移送して、同じ共通長辺の直接評価へ写る。 -/
lemma coherentCospanNativeRightFinalFiberOutput_eq_common :
    coherentCospanNativeRightFinalFiberOutput F X Y Z C b =
      Rr ≫ (coherentCospanNativeRightLongBaseIso F X Y Z C b).hom ≫
        coherentCospanNativeCommonFiberOutput F X Y Z C b := by
  exact relativeTriangleFinalFiberOutput_eq_prism F Z b Dr
    (nativePointedConeTriangle_initial c s hs er) q hq h₁
    (coherentCospanNativeLongBase_right F X Y Z C b) _

end SerrePositivity.InfinityCategories.F2
