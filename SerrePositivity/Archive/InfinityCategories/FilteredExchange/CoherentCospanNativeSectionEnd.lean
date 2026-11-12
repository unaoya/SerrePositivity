module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanNativeFiberCospanEnd
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.StrictKanPullbackEndComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanNativeSectionPullback

/-!
概要：元の native 錐の切断族を、同じ二辺の切断 cospan の end へ比較する。
方針：元の全 pointed 錐の切断の引き戻し表示と、同じ射影を持つ標準 end 比較を合成する。
規約：元の全族を保持。使われ方：実 fiber cospan の end と模型比較の普遍性の移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "c" => coherentCospanConePointwiseCone F X Y Z C b
local notation "d" => joinInr Δ[0] (horn 2 2) ≫ Subtype.val c
local notation "f" => relativeFunctorOverPre pointedSpaceProjection (relativeCospanLeftTarget d)
local notation "g" => relativeFunctorOverPre pointedSpaceProjection (relativeCospanRightTarget d)
local instance : KanComplex (vertexFiber (smallLeftUnstraighteningProjection F) b) :=
  vertexFiber_kanComplex_of_leftFibration _ _
local instance : KanComplex (pullback f g) :=
  HomotopyLimits.kanComplex_of_iso (relativeCospanSectionsIso pointedSpaceProjection d)

/-- 元の native 全錐の同じ全族を、二辺の切断 cospan の同じ end へ送る実際の比較。 -/
def coherentCospanNativeSectionEndComparison : coherentNativeTriangleFiberParameters F b ⟶
    HomotopyLimits.bousfieldKanHolim
      ((AsSmall.down : AsSmall.{u + 1} WalkingCospan ⥤ WalkingCospan) ⋙ cospan f g) :=
  coherentCospanNativeSectionPullback F X Y Z C b ≫ strictKanPullbackEndComparison f g

/-- 各点の元の native 錐が極限なら、同じ切断族から end への比較は単体的ホモトピー同値。 -/
lemma coherentCospanNativeSectionEndComparison_homotopyEquivalence (hc : IsLimitCone c) :
    IsSimplicialHomotopyEquivalence (coherentCospanNativeSectionEndComparison F X Y Z C b) := by
  have : Fibration f := relativeCospanLeftTarget_fibration pointedSpaceProjection d
  have : KanComplex (HomotopyLimits.bousfieldKanHolim
      ((AsSmall.down : AsSmall.{u + 1} WalkingCospan ⥤ WalkingCospan) ⋙ cospan f g)) :=
    HomotopyLimits.bousfieldKanHolim_kanComplex _
  have h := coherentCospanNativeSectionPullback_isQCatEquivalence F X Y Z C b hc
  exact h.isSimplicialHomotopyEquivalence.comp
    (strictKanPullbackEndComparison_homotopyEquivalence f g)

end SerrePositivity.InfinityCategories.F2
