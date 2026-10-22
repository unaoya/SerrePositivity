module

public import SerrePositivity.InfinityCategories.F2.Ind.StrictClassifiedIndCocone
public import SerrePositivity.InfinityCategories.F2.Ind.NativeCoconePreservationTransport
public import SerrePositivity.InfinityCategories.F2.Ind.NativePreservationPosetReduction
public import SerrePositivity.InfinityCategories.F1.FullyFaithfulPostcomposition

/-!
概要：Indκ からの元の関手の κ-filtered 余極限保存性を strict 分類標準余錐で判定する。
方針：cofinal poset 上で図式全体を strict 化し、全部分包含から同型を戻して保存性を移す。
規約：任意の coherent 図式と指定 native 余錐を対象とする。
使われ方：左 Kan 延長の保存性の未証明部分を、同じ strict 全空間の標準余錐に限定する。
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
  {D : SSet.{u + 1}} [Quasicategory D] (G : IndInfinity κ C ⟶ D)

/-- 元の関手の全 κ-filtered 余極限保存性は、同じ strict 分類標準余錐の像で判定できる。 -/
lemma ind_preservesSmallKappaFilteredColimits_iff_strictClassified :
    PreservesSmallKappaFilteredColimits κ G ↔
      ∀ (I : Type u) [PartialOrder I] [IsCardinalFiltered I κ]
        (F : I ⥤ RightFibrationObject C)
        (hF : ∀ v, IsIndVertex κ C
          ((strictCoherentDiagram F ≫ rightStraighteningInfinityMap C).app
            (Opposite.op ⦋0⦌) v)),
        IsColimitCone (mapJoinCocone G (strictClassifiedIndCocone κ F hF)) := by
  constructor
  · intro h I hI hκ F hF
    have : IsKappaFiltered κ (nerve I) := isKappaFiltered_nerve_of_cardinalFiltered I
    exact h (nerve I) _ _ (strictClassifiedIndCocone_isColimit κ F hF)
  · intro h
    apply preservesSmallKappaFilteredColimits_of_poset G
    intro I hI hκ A c hc
    let P := A ≫ indInclusionPresheaf κ C
    let F := presheafDiagramRightStrict P
    let e := presheafDiagramRightStrictClassificationIso P
    have hF : ∀ v, IsIndVertex κ C
        ((strictCoherentDiagram F ≫ rightStraighteningInfinityMap C).app
          (Opposite.op ⦋0⦌) v) := by
      intro v
      exact isIndVertex_isoClosed κ C (e.app v).symm
        (fullSubcomplexOnVertices_vertex (A.app _ v))
    have ei : FunctorIso
        (strictClassifiedIndDiagram κ F hF ≫ indInclusionPresheaf κ C)
        (A ≫ indInclusionPresheaf κ C) := by
      rw [strictClassifiedIndDiagram_inclusion]
      exact e
    let ei' := (indInclusionPresheaf_isFullyFaithful κ C).preimageFunctorIso ei
    exact mapJoinCocone_isColimit_of_functorIso G ei'
      (strictClassifiedIndCocone κ F hF) c
      (strictClassifiedIndCocone_isColimit κ F hF) hc (h I F hF)

end SerrePositivity.InfinityCategories.F2.Ind
