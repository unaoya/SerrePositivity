module

public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeLeftRootNativeCylinder
public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeLeftRestrictionCylinder
public import SerrePositivity.InfinityCategories.F1B.KanFunctorHomotopyClasses

/-!
概要：元の左 Hom 係数を、実際の左三角形と終点固定円柱を通して native な共通脚へ接続する。
方針：HL の同じ円柱から第三辺の始点を同定し、元の二つの比較から作る同型を保持する。
規約：両側で同じ native な共通脚を使い、選んだ円柱の辺の類を公開する。
使われ方：指定輸送経路を共通 path end における左右の Hom 比較の整合性へ移す。
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
  (dB : JoinCocone (i ≫ p)) (hB : IsColimitCone dB) (dC : JoinCocone (j ≫ p))
  (y : SpaceInfinity.{u} _⦋0⦌)
local notation "q" => sliceUnderProjection (f ≫ (i ≫ p))
local notation "U" => coconePointHomFamily (partialColimitSpecifiedPathCocone hp p c hc dB dC) y ≫
  cosliceRestrictionFiberMap p i y
local notation "P" => leftFibrationInitialProjection q c y ≫
  Iso.hom (leftFibrationInitialBaseIso q c y)

/-- 左の第三辺の始点の射影は、元の左 Hom 係数そのもの。 -/
lemma specifiedCoconeLeftRestrictionInitialHomFamily_projection :
    specifiedCoconeLeftRestrictionInitialHomFamily hp p c hc dB hB dC y ≫ P =
      U ≫ coconeMappingSpaceHomComparison dB hB y ≫
        colimitAttachmentHomPrecomposition c hc f (i ≫ p) rfl dB y := by
  have h := congrArg (fun z ↦ SSet.ι₁ ≫ z)
    (specifiedCoconeLeftProjectedCylinder_raw hp p c hc dB hB dC y)
  exact (specifiedCoconeLeftProjectedCylinder hp p c hc dB hB dC y).h₁.symm.trans
    (h.trans (functorHomotopyPrecomp (partialColimitHomEndLeftCylinder p y c hc dB hB) U).h₁)

/-- 実際の第三辺と終点固定円柱から作る、左 Hom 係数と native な共通脚の比較同型。 -/
def specifiedCoconeLeftNativeIso : FunctorIso
    (U ≫ coconeMappingSpaceHomComparison dB hB y ≫
      colimitAttachmentHomPrecomposition c hc f (i ≫ p) rfl dB y)
    (specifiedCoconeNativeRootHomPrecomposition hp p c hc dB dC y) :=
  kanFunctorIsoTransport
    (functorIsoOfSimplicialHomotopy
        (specifiedCoconeLeftRestrictionHomComparison hp p c hc dB hB dC y) ≪≫
      functorIsoOfSimplicialHomotopy (specifiedCoconeLeftRootNativeCylinder hp p c hc dB dC y))
    (specifiedCoconeLeftRestrictionInitialHomFamily_projection hp p c hc dB hB dC y) rfl

/-- 同じ比較同型を表す、左係数から native な共通脚の前合成への全 Hom の円柱。 -/
def specifiedCoconeLeftNativeHomotopy : SSet.Homotopy
    (U ≫ coconeMappingSpaceHomComparison dB hB y ≫
      colimitAttachmentHomPrecomposition c hc f (i ≫ p) rfl dB y)
    (specifiedCoconeNativeRootHomPrecomposition hp p c hc dB dC y) :=
  (specifiedCoconeLeftNativeIso hp p c hc dB hB dC y).simplicialHomotopy

/-- 公開した円柱の辺の類は、実際の第三辺と終点固定比較から作った同じ同型を保つ。 -/
lemma specifiedCoconeLeftNativeHomotopy_hom :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (specifiedCoconeLeftNativeHomotopy hp p c hc dB hB dC y)) =
      (specifiedCoconeLeftNativeIso hp p c hc dB hB dC y).hom :=
  kanFunctorIso_simplicialHomotopy_hom _

end
end SerrePositivity.InfinityCategories.HomotopyLimits
