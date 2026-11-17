module
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftAnodynePushoutProduct

/-!
概要：二重単体集合の対角はReedy left anodyne射をleft anodyne射へ送る。
方針：対角の右随伴の相対matching射を、境界内部Homのleft fibrationへ同定する。
規約：全ホーンのanodyne性への置き換えも、単体集合のモデル構造の仮定も用いない。
使われ方：IS-W2 R03f.2のsimplicial replacementの係数比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.BisimplicialModel
open CategoryTheory Limits HomotopicalAlgebra
open SerrePositivity.Reedy
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations

/-- 対角の右随伴の相対matching射は、元のleft fibration性を保つ。 -/
theorem relativeMatching_leftFibrations {E B : SSet.{u}} (p : E ⟶ B)
    (hp : leftFibrations p) (n : ℕ) :
    leftFibrations (relativeMatchingMap simplexOp (Opposite.op (SimplexCategory.mk n))
      (internalHomRight.map p)) := by
  have : LeftFibration p := ⟨hp⟩
  have h := (leftFibration_pullbackObjObjπ (SSet.boundary n).ι p (boundaryPullbackHom p n)).mem
  exact (leftFibrations.arrow_iso_iff
    (SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.relativeMatchingArrowIso p n)).mpr h

/-- Reedy left anodyneな元の射の対角は、left anodyneである。 -/
theorem diagonal_map_leftAnodyne {A B : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (f : A ⟶ B)
    (hf : reedyLeft simplexOp leftAnodyneExtensions f) :
    leftAnodyneExtensions (diagonal.map f) := by
  intro E T p hp
  have : ∀ j : SimplexCategoryᵒᵖ,
      HasLiftingProperty (relativeLatchingMap simplexOp j f)
        (relativeMatchingMap simplexOp j (internalHomRight.map p)) := by
    intro j
    have hr : leftFibrations
        (relativeMatchingMap simplexOp j (internalHomRight.map p)) := by
      induction j using Opposite.rec with | _ j =>
        induction j using SimplexCategory.rec with | _ n =>
          exact relativeMatching_leftFibrations p hp n
    exact (hf j) _ hr
  have h : HasLiftingProperty f (internalHomRight.map p) := Lifting.hasLiftingProperty simplexOp
  exact (Adjunction.hasLiftingProperty_iff diagonalInternalHomAdjunction f p).mpr h

end SerrePositivity.BisimplicialModel
