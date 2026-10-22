module

public import SerrePositivity.InfinityCategories.F2.Ind.RightStraighteningSmallRecovery
public import SerrePositivity.InfinityCategories.F2.Ind.FilteredElementsCondition
public import SerrePositivity.InfinityCategories.F2.Ind.StrictRightStraighteningColimit
public import SerrePositivity.InfinityCategories.Stable.Cocone

/-!
概要：元の分類値の元の圏の κ-filtered 性は、元の right fibration の全空間の同じ条件。
方針：構成済みの同じ底上の復元同値で輸送し、strict filtered 余極限の実際の前層余錐へ適用する。
規約：任意の同じ strict 分類図式の native 余極限に対応する。一般の strictification は別工程。
使われ方：Indκ の元の圏の κ-filtered 条件の coherent な余極限閉性への入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
open HomotopyLimits
variable {B : SSet.{u}} [Quasicategory B]

/-- 元の分類値の元の圏は、元の全空間と同じ κ-filtered 条件を満たす。 -/
lemma hasKappaFilteredElements_rightStraightening_iff (κ : Cardinal.{u})
    (p : RightFibrationObject B) :
    HasKappaFilteredElements κ
      ((rightStraighteningInfinityMap B).app _ (coherentNerveVertex p)) ↔
        IsKappaFiltered κ p.val.left := by
  change IsKappaFiltered κ
    (smallRightUnstraightening (rightStraighteningPresheafDiagram p)) ↔ _
  exact (isKappaFiltered_iff_of_isQCatEquivalence
    (rightStraighteningSmallRecovery_isQCatEquivalence p)).symm

/-- 同じ通常の κ-filtered 図式の分類像の任意の native 余極限も、元の圏が κ-filtered。 -/
lemma hasKappaFilteredElements_of_strictClassified_colimit
    {κ : Cardinal.{u}} [Fact κ.IsRegular] {I : Type u} [SmallCategory I]
    [IsCardinalFiltered I κ] (F : I ⥤ RightFibrationObject B)
    (hF : ∀ i, HasKappaFilteredElements κ
      ((rightStraighteningInfinityMap B).app _ (coherentNerveVertex (F.obj i))))
    (c : JoinCocone (strictCoherentDiagram F ≫ rightStraighteningInfinityMap B))
    (hc : IsColimitCone c) : HasKappaFilteredElements κ c.vertex := by
  let : IsFiltered I := isFiltered_of_isCardinalFiltered I κ
  have (i : I) : IsKappaFiltered κ (F.obj i).val.left :=
    (hasKappaFilteredElements_rightStraightening_iff κ (F.obj i)).mp (hF i)
  have hv : HasKappaFilteredElements κ (strictRightStraighteningCocone F).vertex := by
    rw [strictRightStraighteningCocone_vertex, hasKappaFilteredElements_rightStraightening_iff]
    exact strictRightFibrationColimit_isKappaFiltered F
  exact hasKappaFilteredElements_isoClosed κ B
    (colimitVertexIso _ c (strictRightStraighteningCocone_isColimit F) hc) hv

/-- 同じ strict 分類図式の native 余極限は、元の単一密度表示で Indκ の最小閉包に属する。 -/
lemma isIndVertex_of_strictClassified_colimit
    {κ : Cardinal.{u}} [Fact κ.IsRegular] {I : Type u} [SmallCategory I]
    [IsCardinalFiltered I κ] (F : I ⥤ RightFibrationObject B)
    (hF : ∀ i, HasKappaFilteredElements κ
      ((rightStraighteningInfinityMap B).app _ (coherentNerveVertex (F.obj i))))
    (c : JoinCocone (strictCoherentDiagram F ≫ rightStraighteningInfinityMap B))
    (hc : IsColimitCone c) : IsIndVertex κ B c.vertex :=
  isIndVertex_of_hasKappaFilteredElements κ
    (hasKappaFilteredElements_of_strictClassified_colimit F hF c hc)

end SerrePositivity.InfinityCategories.F2.Ind
