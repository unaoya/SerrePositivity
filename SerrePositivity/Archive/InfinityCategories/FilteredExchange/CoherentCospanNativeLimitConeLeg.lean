module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanNativeLimitCone
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanApexConeTransportNaturality
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanIntervalConeLeg

/-!
概要：元の余極限頂点の錐の各脚を、元の比較射と区間錐の脚へ指定同型で比較する。
方針：元の可逆頂点円柱の上下三角形と三つの四面体の合成則を使う。
規約：元の指定値を保持。使われ方：元の native 余極限写像と指定 path の回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {B : SSet.{u}} [Quasicategory B] [IsFilteredInfinity B]
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z)
  (hc : ∀ b, IsLimitCone (coherentCospanConePointwiseCone F X Y Z C b))
local notation "f" => coherentCospanNativeLeftKanMap F X Y Z C
local notation "g" => coherentCospanNativeRightKanMap F X Y Z C
local notation "d" => intervalPullbackCone f g
local notation "a" => coherentCospanNativeComparisonKanMap F X Y Z C
local notation "t" => coherentCospanNativeLimitConeTransport F X Y Z C hc
local notation "hv" => Eq.symm (coherentNerveVertex_object (coherentDiagramTotalVertex F))
local notation "hd" => Eq.trans (intervalPullbackCone_vertex f g)
  (spaceInfinityVertex_eq_coherent _)

/-- 元の余極限頂点からの錐の各脚を実際の Kan 射として読む。 -/
def coherentCospanNativeLimitConeKanLeg (i : AsSmall.{u} WalkingCospan) :
    spaceInfinityObject (coherentDiagramTotalVertex F) ⟶ (kanPullbackDiagram f g).obj i :=
  kanApexConeTransportLeg d a t hv i

/-- 元の全錐円柱からの指定脚比較は、元の比較と区間錐の脚の合成を終点に持つ。 -/
def coherentCospanNativeLimitConeLegIso (i : AsSmall.{u} WalkingCospan) :
    FunctorIso (coherentCospanNativeLimitConeKanLeg F X Y Z C hc i)
      (a ≫ intervalPullbackConeKanLeg f g i) :=
  kanApexConeTransportLegIso d a t hv hd i

/-- 元の余極限後の錐の指定三角形からの合成比較。 -/
def coherentCospanNativeLimitConeTriangleIso
    {i j : AsSmall.{u} WalkingCospan} (m : i ⟶ j) :
    FunctorIso (coherentCospanNativeLimitConeKanLeg F X Y Z C hc j)
      (coherentCospanNativeLimitConeKanLeg F X Y Z C hc i ≫ (kanPullbackDiagram f g).map m) :=
  kanApexConeTransportTriangleIso d a t hv m

/-- 指定脚比較は元と区間錐の指定三角形と同じ値で整合する。 -/
lemma coherentCospanNativeLimitConeLegIso_naturality
    {i j : AsSmall.{u} WalkingCospan} (m : i ⟶ j) :
    coherentCospanNativeLimitConeTriangleIso F X Y Z C hc m ≪≫
      (coherentCospanNativeLimitConeLegIso F X Y Z C hc i).postcomp
        ((kanPullbackDiagram f g).map m) =
    coherentCospanNativeLimitConeLegIso F X Y Z C hc j ≪≫
      (kanNativeConeTriangleIso d _ hd m).precomp
        (show (spaceInfinityObject (coherentDiagramTotalVertex F)).obj ⟶
          (intervalPullbackKanObject f g).obj from a) :=
  kanApexConeTransportLegIso_naturality d a t hv hd m

end SerrePositivity.InfinityCategories.F2
