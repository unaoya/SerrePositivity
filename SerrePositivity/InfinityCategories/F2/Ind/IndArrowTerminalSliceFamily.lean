module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowSlicePrismTerminalRelativeIso
public import SerrePositivity.InfinityCategories.F2.Ind.FixedRelativeLiftSquareRestriction

/-!
概要：全終端辺を固定する持ち上げ fiber から、元の領域側の全相対 slice 族を作る。
方針：普遍包含を元の領域へ制限し、sourceTip の全次数の定値性を回収する。
規約：元の全底と全区間 D の指定を保持。使われ方：固定終端辺の普遍 uncurry。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} {C : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C}
  {T : SSet.{u + 1}} {q : T ⟶ diagramComma κ D}
  {H : T ⟶ pullback (indYoneda κ C) (sliceOverProjection D)}
  (W : IndArrowSlicePrism κ D q H)
local notation "p" => stdSimplex.δ 0 ≫ (liftedIntervalToSmall ≫ D)
local notation "b" => indArrowSlicePrismBaseCone (q := q)
local notation "i" => joinMap (arrowInterpolationSourceTip T) (𝟙 Δ[0])
local notation "f" => indArrowSlicePrismCone W
local notation "j" => joinInl (arrowInterpolationCorner T) Δ[0]

/-- 元の全底と全終端辺の指定を保つ、持ち上げの実 fiber。 -/
abbrev indArrowTerminalLiftFamily : SSet.{u + 1} :=
  relativeLiftFixedBoundary (sliceOverProjection p) b i f (indArrowSlicePrismCone_projection W)

/-- 概要：元の全底と全終端辺を固定した持ち上げ空間は可縮 Kan。
方針：元の終端辺包含の right anodyne 性を使う。
規約：同じ実 fiber を保持。使われ方：指定比較の実可逆円柱への表示。 -/
lemma indArrowTerminalLiftFamily_isContractibleKan :
    IsContractibleKan (indArrowTerminalLiftFamily W) :=
  rightAnodyne_relativeLiftFixedBoundary_isContractibleKan (sliceOverProjection p) b i
    (arrowInterpolationTerminalEdge_rightAnodyne T) f (indArrowSlicePrismCone_projection W)

/-- 同じ固定 fiber の全持ち上げを、元の領域上の全相対 slice 関手へ制限する。 -/
def indArrowTerminalSliceFamily : indArrowTerminalLiftFamily W ⟶
    relativeFunctorSpace (sliceOverProjection p) (j ≫ b) :=
  relativeLiftFixedBoundaryInclusion (sliceOverProjection p) b i f
    (indArrowSlicePrismCone_projection W) ≫ relativeFunctorPre (sliceOverProjection p) b j

/-- 普遍族の sourceTip への制限は、元の実持ち上げの同じ全制限に厳密に定値。 -/
lemma indArrowTerminalSliceFamily_sourceTip : indArrowTerminalSliceFamily W ≫
    relativeFunctorPre (sliceOverProjection p) (j ≫ b) (arrowInterpolationSourceTip T) =
      SSet.const (relativeFunctorVertex (sliceOverProjection p)
        (arrowInterpolationSourceTip T ≫ (j ≫ b)) (arrowInterpolationSourceTip T ≫ (j ≫ f))
        (by
          have hp := congrArg (fun h => arrowInterpolationSourceTip T ≫ j ≫ h)
            (indArrowSlicePrismCone_projection W)
          simpa only [Category.assoc] using hp)) := by
  simpa only [indArrowTerminalSliceFamily, Category.assoc] using
    relativeLiftFixedBoundaryInclusion_square (sliceOverProjection p) b i f
      (indArrowSlicePrismCone_projection W) j (arrowInterpolationSourceTip T)
      (joinInl (Δ[0] : SSet.{u + 1}) Δ[0]) (by rw [joinInl_joinMap])

end SerrePositivity.InfinityCategories.F2.Ind
