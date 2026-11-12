module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanNativeFiberCospanComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.HomotopyCospanEndComparison

/-!
概要：実際の fiber cospan と native 切断 cospan の Bousfield–Kan end を比較する。
方針：元の厳密な自然変換の三成分の同値性に、既存の end の同値不変性を適用する。
規約：元の二作用・具体的な三成分を保持。使われ方：元の模型への切断の普遍性の移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "c" => coherentCospanConePointwiseCone F X Y Z C b
local notation "d" => joinInr Δ[0] (horn 2 2) ≫ Subtype.val c
local notation "f" => relativeFunctorOverPre pointedSpaceProjection (relativeCospanLeftTarget d)
local notation "g" => relativeFunctorOverPre pointedSpaceProjection (relativeCospanRightTarget d)
local notation "pX" => smallLeftUnstraighteningProjection X
local notation "pY" => smallLeftUnstraighteningProjection Y
local notation "pZ" => smallLeftUnstraighteningProjection Z
local notation "ql" => vertexFiberMap pX pZ (coherentTransformationTotalMap X Z C.fromLeft)
  (coherentTransformationTotalMap_projection X Z C.fromLeft) b
local notation "qr" => vertexFiberMap pY pZ (coherentTransformationTotalMap Y Z C.fromRight)
  (coherentTransformationTotalMap_projection Y Z C.fromRight) b
local notation "η" => coherentCospanNativeFiberCospanComparison F X Y Z C b
local instance : KanComplex (vertexFiber pX b) := vertexFiber_kanComplex_of_leftFibration _ _
local instance : KanComplex (vertexFiber pY b) := vertexFiber_kanComplex_of_leftFibration _ _
local instance : KanComplex (vertexFiber pZ b) := vertexFiber_kanComplex_of_leftFibration _ _

/-- 元の厳密な比較の三成分は、すべてその実際の比較射による単体的ホモトピー同値。 -/
lemma coherentCospanNativeFiberCospanComparison_app_homotopyEquivalence (i : WalkingCospan) :
    IsSimplicialHomotopyEquivalence ((η).app i) := by
  cases i with
  | none =>
    exact HomotopyLimits.homotopyEquivalence_of_isIso
      (coherentCospanNativeCommonPointFiberIso F X Y Z C b).inv
  | some k =>
    cases k with
    | left =>
      exact coherentCospanNativeLeftFiberEdgeSections_isSimplicialHomotopyEquivalence F X Y Z C b
    | right =>
      exact coherentCospanNativeRightFiberEdgeSections_isSimplicialHomotopyEquivalence F X Y Z C b

/-- 実際の fiber cospan の end から native 切断 cospan の end への同じ三成分による射。 -/
def coherentCospanNativeFiberCospanEndComparison :
    HomotopyLimits.bousfieldKanHolim
      ((AsSmall.down : AsSmall.{u + 1} WalkingCospan ⥤ WalkingCospan) ⋙
        cospan ((SSet.uliftFunctor.{u + 1, u}).map ql) ((SSet.uliftFunctor.{u + 1, u}).map qr)) ⟶
    HomotopyLimits.bousfieldKanHolim
      ((AsSmall.down : AsSmall.{u + 1} WalkingCospan ⥤ WalkingCospan) ⋙ cospan f g) :=
  HomotopyLimits.weightedSectionsMap _ (Functor.whiskerLeft AsSmall.down η)

/-- 同じ実際の三成分の比較は、二つの cospan の end の間の単体的ホモトピー同値。 -/
lemma coherentCospanNativeFiberCospanEndComparison_homotopyEquivalence :
    IsSimplicialHomotopyEquivalence (coherentCospanNativeFiberCospanEndComparison F X Y Z C b) := by
  apply HomotopyLimits.bousfieldKanMap_homotopyEquivalence
  rintro ⟨i⟩
  exact coherentCospanNativeFiberCospanComparison_app_homotopyEquivalence F X Y Z C b i

end SerrePositivity.InfinityCategories.F2
