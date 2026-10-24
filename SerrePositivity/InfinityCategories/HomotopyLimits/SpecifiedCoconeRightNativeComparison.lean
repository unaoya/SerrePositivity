module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRootNativeCylinder
public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRightRestrictionCylinder
public import SerrePositivity.InfinityCategories.HomotopyLimits.HomotopyTriangleClasses
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorHomotopyClasses

/-!
概要：右 HR の終点を既存の右 Hom 係数と同定し、元の三角形の第三辺を native な共通脚へ接続する。
方針：同じ raw 円柱から端点を同定し、実際の第三辺と終点固定の native 比較を合成する。
規約：両円柱と三角形を保持し、合成の辺の類を公開する。
使われ方：共通 path end の右側の Hom 係数と native な共通成分の整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p))
  (hC : IsColimitCone dC) (y : SpaceInfinity.{u} _⦋0⦌)
local notation "q" => sliceUnderProjection (f ≫ (i ≫ p))
local notation "U" => specifiedCoconeRightHomRestriction hp p c hc dB dC y
local notation "V" => specifiedCoconeCommonHomFamily hp p c hc dB dC y
local notation "P" => leftFibrationInitialProjection q c y ≫
  Iso.hom (leftFibrationInitialBaseIso q c y)
local notation "T" => specifiedCoconeRightRestrictionRootedTriangle hp p c hc dB dC hC y

/-- 元の右制限円柱の同じ左 Hom への射影を、正規化した端点で表示する。 -/
def specifiedCoconeRightProjectedCylinder : SSet.Homotopy
    (V ≫ coconeMappingSpaceHomComparison c hc y)
    (specifiedCoconeRightRestrictionInitialHomFamily hp p c hc dB dC hC y ≫ P) :=
  functorHomotopyPostcomp
    (specifiedCoconeRightRestrictionInitialHomCylinder hp p c hc dB dC hC y) P

/-- 正規化後も円柱の raw な射は、共通 end の元の HR に全 Hom を前合成したもの。 -/
lemma specifiedCoconeRightProjectedCylinder_raw :
    (specifiedCoconeRightProjectedCylinder hp p c hc dB dC hC y).h =
      (functorHomotopyPrecomp (partialColimitHomEndRightCylinder hp p y c hc dC hC) U).h :=
  Category.assoc _ _ _

/-- 第三辺の始点の射影は、既存の右側 Hom 係数そのもの。 -/
lemma specifiedCoconeRightRestrictionInitialHomFamily_projection :
    specifiedCoconeRightRestrictionInitialHomFamily hp p c hc dB dC hC y ≫ P =
      U ≫ coconeMappingSpaceHomComparison dC hC y ≫
        colimitAttachmentHomPrecomposition c hc g (j ≫ p) (coconePushoutBoundary_eq hp p) dC y := by
  have h := congrArg (fun k ↦ SSet.ι₁ ≫ k)
    (specifiedCoconeRightProjectedCylinder_raw hp p c hc dB dC hC y)
  exact (specifiedCoconeRightProjectedCylinder hp p c hc dB dC hC y).h₁.symm.trans
    (h.trans (functorHomotopyPrecomp
      (partialColimitHomEndRightCylinder hp p y c hc dC hC) U).h₁)

/-- 元の三角形の三辺の類は、右 HR、第三辺、四面体比較の指定された合成を満たす。 -/
lemma specifiedCoconeRightRootedTriangle_homMk_comp :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (specifiedCoconeRightProjectedCylinder hp p c hc dB dC hC y)) ≫
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (specifiedCoconeRightRestrictionRootedHomComparison hp p c hc dB dC hC y)) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (specifiedCoconeRootedHomCylinderComparison hp p c hc dB dC y)) := by
  apply homotopyTriangle_homMk_comp _ _ _ ((T).family ≫ P)
  · exact (specifiedCoconeRightRestrictionRootedTriangle_first_projection
      hp p c hc dB dC hC y).trans
        (specifiedCoconeRightProjectedCylinder_raw hp p c hc dB dC hC y).symm
  · exact (Category.assoc _ _ _).symm
  · exact specifiedCoconeRightRestrictionRootedTriangle_diagonal_projection hp p c hc dB dC hC y

/-- 既存の右 Hom 係数を、元の第三辺と終点固定円柱を通して native な共通脚へ接続する。 -/
def specifiedCoconeRightNativeIso : FunctorIso
    (U ≫ coconeMappingSpaceHomComparison dC hC y ≫
      colimitAttachmentHomPrecomposition c hc g (j ≫ p) (coconePushoutBoundary_eq hp p) dC y)
    (specifiedCoconeNativeRootHomPrecomposition hp p c hc dB dC y) :=
  SerrePositivity.InfinityCategories.functorIsoTransport
    (functorIsoOfSimplicialHomotopy
        (specifiedCoconeRightRestrictionRootedHomComparison hp p c hc dB dC hC y) ≪≫
      functorIsoOfSimplicialHomotopy (specifiedCoconeRootNativeCylinder hp p c hc dB dC y))
    (specifiedCoconeRightRestrictionInitialHomFamily_projection hp p c hc dB dC hC y) rfl

/-- 同じ二つの実際の比較を合成した同型を表す、右係数から native な共通脚への円柱。 -/
def specifiedCoconeRightNativeHomotopy : SSet.Homotopy
    (U ≫ coconeMappingSpaceHomComparison dC hC y ≫
      colimitAttachmentHomPrecomposition c hc g (j ≫ p) (coconePushoutBoundary_eq hp p) dC y)
    (specifiedCoconeNativeRootHomPrecomposition hp p c hc dB dC y) :=
  (specifiedCoconeRightNativeIso hp p c hc dB dC hC y).simplicialHomotopy

/-- 円柱の辺の類は、元の第三辺と終点固定の native 比較から作った同じ同型を保つ。 -/
lemma specifiedCoconeRightNativeHomotopy_hom :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (specifiedCoconeRightNativeHomotopy hp p c hc dB dC hC y)) =
      (specifiedCoconeRightNativeIso hp p c hc dB dC hC y).hom :=
  SerrePositivity.InfinityCategories.functorIso_simplicialHomotopy_hom _

end
end SerrePositivity.InfinityCategories.HomotopyLimits
