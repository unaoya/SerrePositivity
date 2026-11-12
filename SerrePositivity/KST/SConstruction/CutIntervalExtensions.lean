module
public import SerrePositivity.KST.SConstruction.CutIntervalOrders
public import SerrePositivity.KST.SConstruction.CutSupportImages

/-! # 短い区間から支持部分圏への完全な延長
概要：左右の短い区間の gapped 図式を端点収縮で延長し、対応する支持部分圏に入れる。
方針：反対側の区間が一つの対角に潰れることを全頂点で検査する。
規約：全高次単体を保つ制限・延長。使われ方：支持部分圏との実際の同値。
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

/-- Left 側の短い区間の延長は対応する支持条件を実際に満たす。 -/
lemma cutLeftIntervalExtension_mem (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u})
    (v : (sConstruction (k.val) X.carrier) _⦋0⦌) :
    (cutLeftSupport n k X).predicate
      ((sMap X.carrier (cutLeftIntervalRetraction n k)).app
        (Opposite.op ⦋0⦌) v) := by
  intro a
  have ha : (arNerveMap (cutLeftIntervalRetraction n k)).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ a.val) =
        ComposableArrows.mk₀ (arObj (Fin.last k.val) (Fin.last k.val) le_rfl) := by
    apply ComposableArrows.ext₀
    apply ULift.ext
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      change min a.val.down.val.1.val k.val = k.val
      exact min_eq_right a.property
    · apply Fin.ext
      change min a.val.down.val.2.val k.val = k.val
      exact min_eq_right (a.property.trans a.val.down.property)
  have he := sMap_evaluate_vertex (cutLeftIntervalRetraction n k) v (ComposableArrows.mk₀ a.val)
  have hz : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      ((arNerveMap (cutLeftIntervalRetraction n k)).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ a.val))).app (Opposite.op ⦋0⦌) v.val) := by
    rw [ha]
    exact sConstructionVertex_diagonal_isZero v (Fin.last k.val)
  exact (congrArg _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex he).mpr hz

/-- Left 側の短い区間から支持部分圏への元の端点収縮による延長。 -/
def cutLeftIntervalExtensionMap (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    sConstruction (k.val) X.carrier ⟶ closedSubcategory (cutLeftSupport n k X) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (cutLeftSupport n k X).predicate
    (sMap X.carrier (cutLeftIntervalRetraction n k)) (cutLeftIntervalExtension_mem n k X)

/-- Left 側の延長の包含は元の端点収縮による制限。 -/
lemma cutLeftIntervalExtensionMap_inclusion (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    cutLeftIntervalExtensionMap n k X ≫ (closedStableInclusion (cutLeftSupport n k X)).val =
      sMap X.carrier (cutLeftIntervalRetraction n k) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- Left 側の短い区間から支持部分圏への完全な延長。 -/
def cutLeftIntervalExtension (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    sStableModel (k.val) X ⟶ closedStableModel (cutLeftSupport n k X) :=
  ⟨cutLeftIntervalExtensionMap n k X, by
    apply preservesCofiberData_fullSubcomplex_of_comp (cutLeftSupport n k X).predicate
    change PreservesCofiberData (cutLeftIntervalExtensionMap n k X ≫
      (closedStableInclusion (cutLeftSupport n k X)).val)
    rw [cutLeftIntervalExtensionMap_inclusion]
    exact preservesCofiberData_sMap X.carrier (cutLeftIntervalRetraction n k)⟩

/-- Left 側の支持部分圏から短い区間への元の包含による完全な制限。 -/
def cutLeftIntervalRestriction (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    closedStableModel (cutLeftSupport n k X) ⟶ sStableModel (k.val) X :=
  ⟨(closedStableInclusion (cutLeftSupport n k X)).val ≫
      sMap X.carrier (cutLeftIntervalInclusion n k),
    (closedStableInclusion (cutLeftSupport n k X)).property.comp
      (preservesCofiberData_sMap X.carrier (cutLeftIntervalInclusion n k))⟩

/-- Right 側の短い区間の延長は対応する支持条件を実際に満たす。 -/
lemma cutRightIntervalExtension_mem (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u})
    (v : (sConstruction (n - k.val) X.carrier) _⦋0⦌) :
    (cutRightSupport n k X).predicate
      ((sMap X.carrier (cutRightIntervalRetraction n k)).app
        (Opposite.op ⦋0⦌) v) := by
  intro a
  have ha : (arNerveMap (cutRightIntervalRetraction n k)).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ a.val) =
        ComposableArrows.mk₀ (arObj (0 : Fin (n - k.val + 1)) 0 le_rfl) := by
    apply ComposableArrows.ext₀
    apply ULift.ext
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      change a.val.down.val.1.val - k.val = 0
      exact Nat.sub_eq_zero_of_le (a.val.down.property.trans a.property)
    · apply Fin.ext
      change a.val.down.val.2.val - k.val = 0
      exact Nat.sub_eq_zero_of_le a.property
  have he := sMap_evaluate_vertex (cutRightIntervalRetraction n k) v (ComposableArrows.mk₀ a.val)
  have hz : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      ((arNerveMap (cutRightIntervalRetraction n k)).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ a.val))).app (Opposite.op ⦋0⦌) v.val) := by
    rw [ha]
    exact sConstructionVertex_diagonal_isZero v ((0 : Fin (n - k.val + 1)))
  exact (congrArg _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex he).mpr hz

/-- Right 側の短い区間から支持部分圏への元の端点収縮による延長。 -/
def cutRightIntervalExtensionMap (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    sConstruction (n - k.val) X.carrier ⟶ closedSubcategory (cutRightSupport n k X) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (cutRightSupport n k X).predicate
    (sMap X.carrier (cutRightIntervalRetraction n k)) (cutRightIntervalExtension_mem n k X)

/-- Right 側の延長の包含は元の端点収縮による制限。 -/
lemma cutRightIntervalExtensionMap_inclusion (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    cutRightIntervalExtensionMap n k X ≫ (closedStableInclusion (cutRightSupport n k X)).val =
      sMap X.carrier (cutRightIntervalRetraction n k) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- Right 側の短い区間から支持部分圏への完全な延長。 -/
def cutRightIntervalExtension (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    sStableModel (n - k.val) X ⟶ closedStableModel (cutRightSupport n k X) :=
  ⟨cutRightIntervalExtensionMap n k X, by
    apply preservesCofiberData_fullSubcomplex_of_comp (cutRightSupport n k X).predicate
    change PreservesCofiberData (cutRightIntervalExtensionMap n k X ≫
      (closedStableInclusion (cutRightSupport n k X)).val)
    rw [cutRightIntervalExtensionMap_inclusion]
    exact preservesCofiberData_sMap X.carrier (cutRightIntervalRetraction n k)⟩

/-- Right 側の支持部分圏から短い区間への元の包含による完全な制限。 -/
def cutRightIntervalRestriction (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    closedStableModel (cutRightSupport n k X) ⟶ sStableModel (n - k.val) X :=
  ⟨(closedStableInclusion (cutRightSupport n k X)).val ≫
      sMap X.carrier (cutRightIntervalInclusion n k),
    (closedStableInclusion (cutRightSupport n k X)).property.comp
      (preservesCofiberData_sMap X.carrier (cutRightIntervalInclusion n k))⟩

end SerrePositivity.KST.SConstruction
