module
public import SerrePositivity.KST.SConstruction.ClosedSubcategoryPushouts

/-! # 閉じた全部分圏の零対象の保存
概要：閉じた全部分圏の全ての零対象は周囲でも零対象。
方針：周囲の零対象を内部に戻し、内部の零対象の一意性を包含で写す。
規約：零対象の等号や固定した零角は要求しない。使われ方：包含の完全性と零脚の引き戻し。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 閉じた全部分圏の包含は全ての零対象を保存する。 -/
lemma closedSubcategoryInclusion_preservesZero {X : StableModel.{u}}
    (P : ClosedStablePredicate X) (v : (closedSubcategory P) _⦋0⦌) (hv : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex v) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex v.val := by
  let z := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex X.carrier
  let w := fullSubcategoryVertex P.predicate z.vertex (P.zero_mem z.isZero)
  have hw : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex w :=
    ⟨isInitialVertex_fullSubcomplex_of_ambient P.predicate w z.isInitial,
      isTerminalVertex_fullSubcomplex_of_ambient P.predicate w z.isTerminal⟩
  exact map_isZeroVertex_of_zero_image (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ P.predicate).ι
    w hw z.isZero hv

/-- 閉じた全部分圏の包含は零対象と全押し出しを保存する。 -/
lemma closedSubcategoryInclusion_preservesSConstructionData {X : StableModel.{u}}
    (P : ClosedStablePredicate X) :
    PreservesSConstructionData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X.carrier P.predicate).ι :=
  ⟨closedSubcategoryInclusion_preservesZero P, closedSubcategoryInclusion_preservesPushout P⟩

end SerrePositivity.KST.SConstruction
