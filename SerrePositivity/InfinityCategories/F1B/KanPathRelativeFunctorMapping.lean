module

public import SerrePositivity.InfinityCategories.F1B.KanRelativeLeftPathReplacement
public import SerrePositivity.InfinityCategories.F1B.KanRelativeRightPathReplacement
public import SerrePositivity.InfinityCategories.F1B.KanRelativeRightFunctorMapping
public import SerrePositivity.InfinityCategories.Core.FunctorComposition
public import SerrePositivity.InfinityCategories.F1B.KanRelativeFunctorTarget

/-!
概要：一般 U の標準相対 Kan 関手の写像空間を path 置換上の相対標的へ比較する。
方針：定値 path の切断の後合成の同値と置換後の片側比較を合成する。
規約：U に充填性を要求せず、相対標的は path 置換後のものを明示する。
使われ方：一般 U の比較四角形の homotopy pullback 性への帰着。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：元の関手を定値 path に写して置換後の相対内部 Hom へ制限する射。
方針：切断への後合成に置換後の相対制限を合成する。
規約：path 置換上の相対標的の選択を明示する。
使われ方：一般 U の元の写像空間の比較射。 -/
def kanPathRelativeFunctorRestriction {K C D E : SSet.{u}} (U : D ⟶ E) (δ : K ⟶ C)
    (t : internalHom.PullbackObjObj δ (equivalencePathReplacementMap U)) :
    (ihom C).obj D ⟶ t.pt := (ihom C).map (equivalencePathReplacementSection U) ≫ t.π

/-- 概要：一般 U の相対左 Kan 関手から出る path 置換上の相対比較はホモトピー同値。
方針：切断による標準左条件の保存と置換上の片側比較に後合成の同値を合成する。
規約：相手 G の普遍性は仮定しない。
使われ方：一般 U の相対写像空間比較の左側。 -/
lemma kanPathRelativeLeftFunctor_pinchedHomMap_equivalence {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (δ : K ⟶ C) [Mono δ] [InnerFibration δ] (hδ : IsFullyFaithful δ)
    (U : D ⟶ E) (t : internalHom.PullbackObjObj δ (equivalencePathReplacementMap U))
    (F G : C ⟶ D) (hF : IsRelativeLeftKanExtendedFrom U δ F) :
    IsSimplicialHomotopyEquivalence
      (pinchedHomMap (kanPathRelativeFunctorRestriction U δ t)
        (functorVertex F) (functorVertex G)) := by
  have : Quasicategory t.pt := kanRelativeInternalHomTarget_quasicategory_of_mono
    (equivalencePathReplacementMap U) δ t
  have hs := (kanEquivalencePathReplacementSection_isQCatEquivalence U).postcompose C
  have hl := kanRelativeLeftFunctor_relative_pinchedHomMap_equivalence δ hδ
    (equivalencePathReplacementMap U) (kanEquivalenceLifting_equivalencePathReplacementMap U) t
    (F ≫ equivalencePathReplacementSection U) (G ≫ equivalencePathReplacementSection U)
    ((kanIsRelativeLeftKanExtendedFrom_pathSection_iff U δ F).2 hF)
  rw [kanPathRelativeFunctorRestriction, pinchedHomMap_comp]
  exact (hs.isFullyFaithful (functorVertex F) (functorVertex G)).comp hl

/-- 概要：一般 U の相対右 Kan 関手へ入る path 置換上の相対比較はホモトピー同値。
方針：切断による標準右条件の保存と置換上の片側比較に後合成の同値を合成する。
規約：始点 F の普遍性は仮定しない。
使われ方：一般 U の相対写像空間比較の右側。 -/
lemma kanPathRelativeRightFunctor_pinchedHomMap_equivalence {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (δ : K ⟶ C) [Mono δ] [InnerFibration δ] (hδ : IsFullyFaithful δ)
    (U : D ⟶ E) (t : internalHom.PullbackObjObj δ (equivalencePathReplacementMap U))
    (F G : C ⟶ D) (hG : IsRelativeRightKanExtendedFrom U δ G) :
    IsSimplicialHomotopyEquivalence
      (pinchedHomMap (kanPathRelativeFunctorRestriction U δ t)
        (functorVertex F) (functorVertex G)) := by
  have : Quasicategory t.pt := kanRelativeInternalHomTarget_quasicategory_of_mono
    (equivalencePathReplacementMap U) δ t
  have hs := (kanEquivalencePathReplacementSection_isQCatEquivalence U).postcompose C
  have hr := kanRelativeRightFunctor_relative_pinchedHomMap_equivalence δ hδ
    (equivalencePathReplacementMap U) (kanEquivalenceLifting_equivalencePathReplacementMap U) t
    (F ≫ equivalencePathReplacementSection U) (G ≫ equivalencePathReplacementSection U)
    ((kanIsRelativeRightKanExtendedFrom_pathSection_iff U δ G).2 hG)
  rw [kanPathRelativeFunctorRestriction, pinchedHomMap_comp]
  exact (hs.isFullyFaithful (functorVertex F) (functorVertex G)).comp hr

end SerrePositivity.InfinityCategories.F1B
