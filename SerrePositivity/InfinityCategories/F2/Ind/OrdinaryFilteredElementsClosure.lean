module

public import SerrePositivity.InfinityCategories.F2.Ind.PresheafDiagramStrictification
public import SerrePositivity.InfinityCategories.F2.Ind.ClassifiedFilteredElements
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanDiagramColimitTransport

/-!
概要：通常の κ-filtered 添字上の任意の coherent 前層図式で、元の圏の κ-filtered 性は余極限で保たれる。
方針：元の図式の大域 strict 化で頂点を保つ余極限余錐を輸送し、同じ分類図式の保存を使う。
規約：元の coherent 図式や native 余錐に strict 性を仮定しない。
使われ方：一般の小さい κ-filtered 添字の cofinal poset への制限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
open HomotopyLimits
variable {C : SSet.{u}} [Quasicategory C]

/-- 元の coherent 図式の各値の条件を、同じ大域 strict 化の実際の分類値へ移す。 -/
lemma hasKappaFilteredElements_strictification_values {κ : Cardinal.{u}}
    {I : Type u} [Category.{u} I]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ PresheafInfinity C)
    (hF : ∀ i : (nerve I) _⦋0⦌,
      HasKappaFilteredElements κ (F.app (Opposite.op ⦋0⦌) (ULift.up i))) (i : I) :
    HasKappaFilteredElements κ ((rightStraighteningInfinityMap C).app _
      (coherentNerveVertex ((presheafDiagramRightStrict F).obj i))) := by
  have h := (presheafDiagramRightStrictClassificationIso F).app (ULift.up (nerveVertex i))
  have hv := congrArg ((rightStraighteningInfinityMap C).app (Opposite.op ⦋0⦌))
    (strictCoherentDiagram_vertex (presheafDiagramRightStrict F) i)
  have e := (eqToIso (congrArg HomotopyCategory.mk hv)).symm ≪≫ h
  exact hasKappaFilteredElements_isoClosed κ C e.symm (hF (nerveVertex i))

/-- 同じ通常の κ-filtered 添字上の任意の native 前層余極限で、元の圏は κ-filtered。 -/
lemma hasKappaFilteredElements_of_ordinary_colimit
    {κ : Cardinal.{u}} [Fact κ.IsRegular] {I : Type u} [SmallCategory I]
    [IsCardinalFiltered I κ]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ PresheafInfinity C)
    (c : JoinCocone F) (hc : IsColimitCone c)
    (hF : ∀ i : (nerve I) _⦋0⦌,
      HasKappaFilteredElements κ (F.app (Opposite.op ⦋0⦌) (ULift.up i))) :
    HasKappaFilteredElements κ c.vertex := by
  obtain ⟨d, hd, hv⟩ := exists_colimitCocone_functorIso_sameVertex
    (presheafDiagramRightStrictClassificationIso F).symm c hc
  rw [← hv]
  exact hasKappaFilteredElements_of_strictClassified_colimit (presheafDiagramRightStrict F)
    (hasKappaFilteredElements_strictification_values F hF) d hd

end SerrePositivity.InfinityCategories.F2.Ind
