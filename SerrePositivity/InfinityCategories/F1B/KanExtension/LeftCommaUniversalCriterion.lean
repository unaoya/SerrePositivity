module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftCommaUniversalFamily
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftCommaUniversalIdentity
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftCommaRelativeCriterion
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeLeftCanonical
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeLeftHomotopyInvariant
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeLeftJoinCriterion

/-!
概要：普遍図式への前合成が標準の相対左 Kan 条件を保ち反映することを示す。
方針：候補の指定変換の類は恒等であり、comma fiber の局所判定を使う。
規約：同じ底での選択を全ての標的・関手に使う。
使われ方：元の Kan 関手の全部分圏と相対 join 図式の全部分圏の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：普遍自己変換を任意の関手で写した変換の類も恒等射。
方針：後合成の関手はホモトピー圏の恒等射を保つ。
規約：raw な変換が定値であるとは仮定しない。
使われ方：普遍図式から得た候補の変換を恒等の指定変換と比較する。 -/
lemma kanLeftCommaUniversalIdentityHomotopy_postcomp_hom {K C D : SSet.{u}}
    [Quasicategory C] (δ : K ⟶ C) (F : C ⟶ D) :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (functorHomotopyPostcomp (kanLeftCommaUniversalIdentityHomotopy δ) F)) =
        SSet.Truncated.HomotopyCategory.homMk
          (functorEdgeOfSimplicialHomotopy (functorHomotopyRefl (δ ≫ F))) := by
  rw [functorHomotopyPostcomp_hom, kanLeftCommaUniversalIdentityHomotopy_hom,
    functorHomotopyRefl_hom]
  exact CategoryTheory.Functor.map_id _ _

/-- 概要：標準の相対左 Kan 条件は普遍図式への前合成後の全 fiber の U 余極限性と同値。
方針：候補の関手は厳密に F であり、候補の指定変換の類は恒等射である。
規約：U は inner fibration。δ の単射性はこの局所比較には不要。
使われ方：元の相対左 Kan 関手の族を相対 join の普遍図式の族へ写す。 -/
lemma kanIsRelativeLeftKanExtendedFrom_iff_universal_fibers {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (U : D ⟶ E) [InnerFibration U] (δ : K ⟶ C) (F : C ⟶ D) :
    IsRelativeLeftKanExtendedFrom U δ F ↔
      ∀ c : C _⦋0⦌, IsRelativeColimitCone U (kanRelativeJoinFiberCocone
        (kanLeftCommaProjection δ) c (kanLeftCommaUniversalDiagram δ ≫ F)) := by
  let H := kanLeftCommaUniversalDiagram δ ≫ F
  have hH : relativeJoinInl (kanLeftCommaProjection δ) (𝟙 C) ≫ H =
      kanLeftCommaSource δ ≫ (δ ≫ F) := kanLeftCommaUniversalFamily_diagram δ F
  let β := kanLeftCommaCandidateTransformation δ (δ ≫ F) H hH
  let α := functorHomotopyPostcomp (kanLeftCommaUniversalIdentityHomotopy δ) F
  have he := kanIsRelativeLeftKanExtension_iff_of_diagram_eq_of_h_eq U δ rfl
    (kanLeftCommaUniversalFamily_candidate δ F) β α (by rfl)
  have hh := kanIsRelativeLeftKanExtension_iff_of_homMk_eq U δ (δ ≫ F) F α
    (functorHomotopyRefl (δ ≫ F)) (kanLeftCommaUniversalIdentityHomotopy_postcomp_hom δ F)
  exact (kanIsRelativeLeftKanExtendedFrom_iff_refl_extension U δ F).trans
    (hh.symm.trans (he.symm.trans
      (kanLeftCommaCandidate_isRelativeLeftKanExtension_iff U δ (δ ≫ F) H hH)))

end SerrePositivity.InfinityCategories.F1B
