module
public import SerrePositivity.KST.SConstruction.AdditivityNaturality

/-! # S₂ の二つの区間への加法性
概要：S₂ C の中央 cofiber 四角形の subobject・quotient は正の反復実現後に積への弱同値。
方針：元の中央四角形への自明ファイブレーションと反復加法性を合成する。
規約：S₂ C 自体と C×C の同値は主張しない。使われ方：Segal 分解と delooping の面条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open scoped Simplicial

/-- S₂ の完全な中央四角形の制限は全ての角の評価と厳密に可換。 -/
lemma sTwoCofiberComparison_evaluation (X : StableModel.{u})
    (q : (Δ[1] ⊗ Δ[1] : SSet.{u}) _⦋0⦌) :
    (sTwoCofiberComparison X ≫ cofiberStableEvaluation X q).val =
      (gappedSubcomplex 2 X.carrier).ι ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (arTwoMiddleSquare.app (Opposite.op ⦋0⦌) q) := by
  change (sTwoCofiberRestriction X.carrier ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt q = _
  rw [sTwoCofiberRestriction_ι, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt]

/-- S₂ の中央四角形の subobject・quotient の正の反復実現における射対。 -/
def sTwoRealizationAdditivityMap (r : ℕ) (X : StableModel.{u}) :
    (multiRealizationFunctor (r + 1)).obj (sStableModel 2 X) ⟶
      (multiRealizationFunctor (r + 1)).obj X ⊗ (multiRealizationFunctor (r + 1)).obj X :=
  CartesianMonoidalCategory.lift
    ((multiRealizationFunctor (r + 1)).map (sTwoCofiberComparison X ≫ cofiberStableSubobject X))
    ((multiRealizationFunctor (r + 1)).map (sTwoCofiberComparison X ≫ cofiberStableQuotient X))

/-- S₂ の射対は元の四角形比較と全 cofiber 図式の加法性の合成。 -/
lemma sTwoRealizationAdditivityMap_eq (r : ℕ) (X : StableModel.{u}) :
    sTwoRealizationAdditivityMap r X =
      (multiRealizationFunctor (r + 1)).map (sTwoCofiberComparison X) ≫
        multiRealizationAdditivityMap (r + 1) X := by
  rw [sTwoRealizationAdditivityMap, multiRealizationAdditivityMap,
    CartesianMonoidalCategory.comp_lift, ← Functor.map_comp, ← Functor.map_comp]

/-- 全ての正の反復実現で S₂ の二つの区間への射対は局所化同型。 -/
lemma sTwoRealizationAdditivityMap_localized_isIso (r : ℕ) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (sTwoRealizationAdditivityMap r X)) := by
  have := sTwoCofiberComparison_realization_localized_isIso (r + 1) X
  have := multiRealizationAdditivityMap_localized_isIso r X
  rw [sTwoRealizationAdditivityMap_eq, AnodyneHomotopy.anodyneQ.map_comp]
  infer_instance

end SerrePositivity.KST.SConstruction
