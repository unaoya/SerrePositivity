module

public import SerrePositivity.InfinityCategories.F2.Ind.FilteredElementsClosure
public import SerrePositivity.InfinityCategories.F2.Ind.KappaColimits

/-!
概要：通常の κ-filtered right fibration 図式の同じ標準分類余錐を Indκ 内へ戻す。
方針：全部分包含への図式の持ち上げと、実際の分類余極限頂点の閉性を使う。
規約：元の全余錐とその脚を保持する。使われ方：延長の保存性の strict な試験余錐。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
open HomotopyLimits
variable (κ : Cardinal.{u}) [Fact κ.IsRegular] {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [PartialOrder I] [IsCardinalFiltered I κ]
  (F : I ⥤ RightFibrationObject C)
  (hF : ∀ v, IsIndVertex κ C
    ((strictCoherentDiagram F ≫ rightStraighteningInfinityMap C).app (Opposite.op ⦋0⦌) v))

/-- 同じ strict 分類図式の全部分 Indκ 内への持ち上げ。 -/
def strictClassifiedIndDiagram :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ IndInfinity κ C :=
  fullSubcomplexLift (IsIndVertex κ C)
    (strictCoherentDiagram F ≫ rightStraighteningInfinityMap C) hF

omit [Fact κ.IsRegular] [IsCardinalFiltered I κ] in
lemma strictClassifiedIndDiagram_inclusion :
    strictClassifiedIndDiagram κ F hF ≫ indInclusionPresheaf κ C =
      strictCoherentDiagram F ≫ rightStraighteningInfinityMap C :=
  fullSubcomplexLift_ι _ _ _

omit [IsCardinalFiltered I κ] in
include hF in
/-- 試験図式の各値の元の right fibration の全空間は κ-filtered。 -/
lemma strictClassifiedIndDiagram_total_isKappaFiltered (i : I) :
    IsKappaFiltered κ (F.obj i).val.left := by
  have hp := (isIndVertex_iff_hasKappaFilteredElements κ C _).mp
    (hF (ULift.up (nerveVertex i)))
  have hv := congrArg ((rightStraighteningInfinityMap C).app (Opposite.op ⦋0⦌))
    (strictCoherentDiagram_vertex F i)
  exact (hasKappaFilteredElements_rightStraightening_iff κ (F.obj i)).mp (hv ▸ hp)

/-- 元の標準分類余錐を持ち上げた Indκ 内の同じ余錐。 -/
def strictClassifiedIndCocone : JoinCocone (strictClassifiedIndDiagram κ F hF) := by
  let : IsFiltered I := isFiltered_of_isCardinalFiltered I κ
  let c := coherentCoconeOfDiagramEq
    (strictClassifiedIndDiagram_inclusion κ F hF).symm (strictRightStraighteningCocone F)
  have hc : IsColimitCone c :=
    (coherentCoconeOfDiagramEq_isColimit_iff _ _).mp
      (strictRightStraighteningCocone_isColimit F)
  have : IsKappaFiltered κ (nerve I) := isKappaFiltered_nerve_of_cardinalFiltered I
  have hv : IsIndVertex κ C c.vertex :=
    isIndVertex_kappaColimitClosed κ C (nerve I)
      (strictClassifiedIndDiagram κ F hF ≫ indInclusionPresheaf κ C) c hc
      (fun i => fullSubcomplexOnVertices_vertex
        ((strictClassifiedIndDiagram κ F hF).app _ (ULift.up i)))
  exact fullCoconeLift (IsIndVertex κ C) (strictClassifiedIndDiagram κ F hF) c hv

/-- 同じ標準余錐の Indκ 内への持ち上げは native な余極限。 -/
lemma strictClassifiedIndCocone_isColimit :
    IsColimitCone (strictClassifiedIndCocone κ F hF) := by
  let : IsFiltered I := isFiltered_of_isCardinalFiltered I κ
  unfold strictClassifiedIndCocone
  apply fullCoconeLift_isColimit
  exact (coherentCoconeOfDiagramEq_isColimit_iff _ _).mp
    (strictRightStraighteningCocone_isColimit F)

/-- 全部分包含後の全余錐の射は元の標準分類余錐の射そのもの。 -/
lemma strictClassifiedIndCocone_inclusion_val :
    letI : IsFiltered I := isFiltered_of_isCardinalFiltered I κ
    (strictClassifiedIndCocone κ F hF).val ≫ indInclusionPresheaf κ C =
      (strictRightStraighteningCocone F).val := by
  let : IsFiltered I := isFiltered_of_isCardinalFiltered I κ
  unfold strictClassifiedIndCocone
  change (mapJoinCocone (indInclusionPresheaf κ C) (fullCoconeLift _ _ _ _)).val = _
  dsimp only [indInclusionPresheaf, IndInfinity] at *
  rw [fullCoconeLift_inclusion]
  rfl

end SerrePositivity.InfinityCategories.F2.Ind
