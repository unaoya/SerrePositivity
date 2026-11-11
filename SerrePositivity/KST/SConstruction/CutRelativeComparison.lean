module
public import SerrePositivity.KST.SConstruction.CutSupportImages
public import SerrePositivity.KST.SConstruction.RelativeCofiberModel

/-! # 左右の支持部分圏による相対切断比較
概要：任意の切断 cofiber 比較を左右の支持条件の相対 E に持ち上げる。
方針：両端の厳密な評価式と支持条件を使い、完全性は包含後から反映する。
規約：相対条件を入力に仮定しない。使われ方：中央評価との同値と Segal 射。
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

/-- 切断比較の全頂点は実際に左右の支持部分圏による相対条件を満たす。 -/
lemma cutStableComparison_relative_mem (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u})
    (v : (sConstruction n X.carrier) _⦋0⦌) :
    (relativeCofiberPredicate (cutLeftSupport n k X) (cutRightSupport n k X)).predicate
      ((cutStableComparison n k X).val.app (Opposite.op ⦋0⦌) v) := by
  have hs := congrArg (fun f : sStableModel n X ⟶ sStableModel n X =>
    f.val.app (Opposite.op ⦋0⦌) v) (cutStableComparison_evaluation n k X 0 0)
  have hq := congrArg (fun f : sStableModel n X ⟶ sStableModel n X =>
    f.val.app (Opposite.op ⦋0⦌) v) (cutStableComparison_evaluation n k X 1 1)
  exact ⟨(congrArg (cutLeftSupport n k X).predicate hs).mpr (cutLeftSupport_sMap n k X v),
    (congrArg (cutRightSupport n k X).predicate hq).mpr (cutRightSupport_sMap n k X v)⟩

/-- 同じ図式内の切断比較を左右支持の相対 E に持ち上げる。 -/
def cutRelativeComparisonMap (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    sConstruction n X.carrier ⟶
      relativeCofiberDiagrams (cutLeftSupport n k X) (cutRightSupport n k X) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift
    (relativeCofiberPredicate (cutLeftSupport n k X) (cutRightSupport n k X)).predicate
    (cutStableComparison n k X).val (cutStableComparison_relative_mem n k X)

/-- 相対比較は包含後に元の完全な切断比較を厳密に回収する。 -/
lemma cutRelativeComparisonMap_inclusion (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    cutRelativeComparisonMap n k X ≫
        (relativeCofiberInclusion (cutLeftSupport n k X) (cutRightSupport n k X)).val =
      (cutStableComparison n k X).val :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 左右の支持部分圏の相対 E への切断比較は完全関手。 -/
def cutRelativeComparison (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    sStableModel n X ⟶
      relativeCofiberStableModel (cutLeftSupport n k X) (cutRightSupport n k X) :=
  ⟨cutRelativeComparisonMap n k X, by
    apply preservesCofiberData_fullSubcomplex_of_comp
      (relativeCofiberPredicate (cutLeftSupport n k X) (cutRightSupport n k X)).predicate
    change PreservesCofiberData (cutRelativeComparisonMap n k X ≫
      (relativeCofiberInclusion (cutLeftSupport n k X) (cutRightSupport n k X)).val)
    rw [cutRelativeComparisonMap_inclusion]
    exact (cutStableComparison n k X).property⟩

/-- 完全な相対切断比較も包含後に元の切断を厳密に回収する。 -/
lemma cutRelativeComparison_inclusion (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    cutRelativeComparison n k X ≫
        relativeCofiberInclusion (cutLeftSupport n k X) (cutRightSupport n k X) =
      cutStableComparison n k X :=
  Subtype.ext (cutRelativeComparisonMap_inclusion n k X)

/-- 左右の支持部分圏の相対 E から中央の S_n C を評価する完全関手。 -/
def cutRelativeMiddle (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    relativeCofiberStableModel (cutLeftSupport n k X) (cutRightSupport n k X) ⟶ sStableModel n X :=
  relativeCofiberInclusion (cutLeftSupport n k X) (cutRightSupport n k X) ≫
    cofiberStableMiddle (sStableModel n X)

/-- 相対切断比較は中央評価の厳密な切断。 -/
lemma cutRelativeComparison_middle (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    cutRelativeComparison n k X ≫ cutRelativeMiddle n k X = 𝟙 (sStableModel n X) := by
  change cutRelativeComparison n k X ≫
    (relativeCofiberInclusion (cutLeftSupport n k X) (cutRightSupport n k X) ≫
      cofiberStableMiddle (sStableModel n X)) = _
  rw [← Category.assoc, cutRelativeComparison_inclusion, cutStableComparison_middle]

end SerrePositivity.KST.SConstruction
