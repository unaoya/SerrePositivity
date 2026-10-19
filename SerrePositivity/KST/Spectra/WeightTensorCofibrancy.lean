module

public import SerrePositivity.KST.Spectra.WeightTensorLatching
public import SerrePositivity.KST.Spectra.PushoutProductMonomorphism

/-!
概要：Reedy cofibrant な重みの tensor は単射および anodyne なパラメーターを Reedy 左類へ送る。
方針：実際の latching の pushout-product 表示へ単体集合の二つの積定理を適用する。
規約：対象ごとの単射性ではなく、重みの latching の単射性を用いる。
使われ方：Goerss–Jardine VII §4。重みの境界 cylinder と horn cylinder の充填。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet
open SerrePositivity.Reedy

namespace SerrePositivity.KST.Spectra.WeightTensorLatching
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (F : CosimplicialObject SSet.{u})
    (hF : reedyLeft simplex (MorphismProperty.monomorphisms SSet.{u}) (initial.to F))

include hF

/-- Reedy cofibrant な重みでは単射のパラメーターが Reedy 単射になる。 -/
lemma map_reedy_mono {A B : SSet.{u}} (i : A ⟶ B) [Mono i] :
    reedyLeft simplex (MorphismProperty.monomorphisms SSet.{u}) (map F i) := by
  intro j
  let : Mono ((latchingComparison simplex j).app F) :=
    ((MorphismProperty.monomorphisms SSet.{u}).arrow_iso_iff
      (BousfieldKanWeightLatching.initialArrowIso F j)).mpr (hF j)
  exact ((MorphismProperty.monomorphisms SSet.{u}).arrow_iso_iff
    (relativeProductArrowIso F i j)).mpr (PushoutProductMonomorphism.mono (productSquare F i j))

/-- Reedy cofibrant な重みでは anodyne なパラメーターが Reedy anodyne になる。 -/
lemma map_reedy_anodyne {A B : SSet.{u}} (i : A ⟶ B) (hi : anodyneExtensions i) :
    reedyLeft simplex anodyneExtensions (map F i) := by
  intro j
  let : Mono ((latchingComparison simplex j).app F) :=
    ((MorphismProperty.monomorphisms SSet.{u}).arrow_iso_iff
      (BousfieldKanWeightLatching.initialArrowIso F j)).mpr (hF j)
  exact (anodyneExtensions.arrow_iso_iff (relativeProductArrowIso F i j)).mpr
    (anodyneExtensions_pushoutObjObjι (productSquare F i j) hi)

end
end SerrePositivity.KST.Spectra.WeightTensorLatching
