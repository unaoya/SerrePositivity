module

public import SerrePositivity.AlgebraicGeometry.DegreeOneProjectiveModelFiberPowers
public import SerrePositivity.AlgebraicGeometry.ReesFiniteDegreeOnePresentation

/-!
概要：実際の affine blowup と、その既存の Čech nerve の各項の次数一表示。
方針：既存の Rees 全射表示を、同じ構造射の等式と有限冪の表示の帰納へ渡す。
規約：表示の存在を仮定にせず、有限生成中心から供給する。
使われ方：2f の射影版の四角形を、幾何の blowup の有限ファイバー冪へ適用する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Opposite
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

/-- 有限生成中心の実際の blowup 射は、有限な次数一表示を持つ。 -/
theorem nonempty_affineBlowupDegreeOneProjectiveModel (hI : I.FG) :
    Nonempty (DegreeOneProjectiveModel (affineBlowupπ I)) := by
  obtain ⟨n, a, hs⟩ := exists_rees_degreeOne_polynomial_surjective I hI
  refine ⟨?_⟩
  exact (schemeScalarMorphism_rees I) ▸
    degreeOneProjectiveModelOfProj (reesGrade I) (fun j ↦ reesDegreeOne I (a j))
      (fun j ↦ reesDegreeOne_mem I (a j)) hs

/-- 実際の blowup の既存の Čech nerve の各項は、同じ基底上の表示を持つ。 -/
theorem nonempty_affineBlowupCechTermModel (hI : I.FG) (n : SimplexCategoryᵒᵖ) :
    Nonempty (DegreeOneProjectiveModel
      ((Arrow.mk (affineBlowupπ I)).augmentedCechNerve.hom.app n)) := by
  obtain ⟨m⟩ := nonempty_affineBlowupDegreeOneProjectiveModel I hI
  exact ⟨m.cechTerm n⟩

end SerrePositivity.AlgebraicGeometry
