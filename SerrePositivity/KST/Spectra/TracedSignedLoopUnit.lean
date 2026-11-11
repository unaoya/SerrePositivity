module

public import SerrePositivity.KST.Spectra.SpectrumTracedRectification
public import SerrePositivity.KST.Spectra.SignedLoopUnitStructurePath
public import SerrePositivity.KST.Spectra.SignedLoopModel

/-!
概要：共通の指定構造区間と各段の延長トレース・実三角形を保持する BF loop 単位。
方針：同じ signedLoopModel を標的として tracedRectifyInto を適用する。
規約：従来の signedLoopUnit との全 Hom 一致は仮定しない。元の evaluationPost は変更しない。
使われ方：指定境界を保つ Kan 随伴の全 Hom 比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
variable (X : OmegaSpectrum.{u})

/-- 元の Kan 随伴の同じ構造区間を入力し、全段の実区間を保持した BF 単位。 -/
def tracedSignedLoopUnit : X ⟶ signedLoopModel X :=
  tracedRectifyInto X (KanSequence.signedLoopTail X.toKanSequence)
    (KanSequence.signedLoopTail_omegaCondition X.toKanSequence_omega)
    (KanSequence.kanAdjoint X.toKanSequence) (signedLoopUnitStructurePath X)

/-- 同じ構造区間から得た、置換前の厳密なトレース付き列射へ戻る。 -/
lemma tracedSignedLoopUnit_projection (n : ℕ) :
    (tracedSignedLoopUnit X).app n ≫ (signedLoopProjection X).app n =
    (KanSequence.tracedRectify (X := X.toKanSequence)
      (Y := KanSequence.signedLoopTail X.toKanSequence) X.sigma_mono
      (KanSequence.kanAdjoint X.toKanSequence) (signedLoopUnitStructurePath X)).app n :=
  tracedRectifyInto_projection X (KanSequence.signedLoopTail X.toKanSequence)
    (KanSequence.signedLoopTail_omegaCondition X.toKanSequence_omega)
    (KanSequence.kanAdjoint X.toKanSequence) (signedLoopUnitStructurePath X) n

/-- 元の各段の Kan 随伴から、同じ BF 単位の raw 射影への実区間。 -/
def tracedSignedLoopUnitComparison (n : ℕ) :
    PointedMapping.VerticalPath
      (PointedObject.toPoint ((KanSequence.signedLoopTail X.toKanSequence).level n).space)
      (KanSequence.kanAdjoint X.toKanSequence n)
      ((tracedSignedLoopUnit X).app n ≫ (signedLoopProjection X).app n) :=
  tracedRectifyIntoComparison X (KanSequence.signedLoopTail X.toKanSequence)
    (KanSequence.signedLoopTail_omegaCondition X.toKanSequence_omega)
    (KanSequence.kanAdjoint X.toKanSequence) (signedLoopUnitStructurePath X) n

/-- 同じ前段の比較区間を懸垂と標的構造射で移した、実三角形の第二辺。 -/
def tracedSignedLoopUnitStepInterval (n : ℕ) :=
  KanSequence.tracedRectificationStepPath (X := X.toKanSequence)
    (Y := KanSequence.signedLoopTail X.toKanSequence) (KanSequence.kanAdjoint X.toKanSequence) n
    (KanSequence.tracedRectificationStage (X := X.toKanSequence)
      (Y := KanSequence.signedLoopTail X.toKanSequence) X.sigma_mono
      (KanSequence.kanAdjoint X.toKanSequence) (signedLoopUnitStructurePath X) n)

/-- 同じ次段の比較区間を構造射へ制限した、実三角形の対角辺。 -/
def tracedSignedLoopUnitRestrictionInterval (n : ℕ) :=
  KanSequence.tracedRectifyRestrictionPath (X := X.toKanSequence)
    (Y := KanSequence.signedLoopTail X.toKanSequence) X.sigma_mono
    (KanSequence.kanAdjoint X.toKanSequence) (signedLoopUnitStructurePath X) n

/-- 次段延長の制限として保持された対角区間と、同じ二辺を持つ実構造三角形。 -/
def tracedSignedLoopUnitTriangle (n : ℕ) :=
  KanSequence.tracedRectifyComparison_triangle (X := X.toKanSequence)
    (Y := KanSequence.signedLoopTail X.toKanSequence) X.sigma_mono
    (KanSequence.kanAdjoint X.toKanSequence) (signedLoopUnitStructurePath X) n

/-- 同じ実比較区間の全体を、構造単射へ制限すると元の合成区間全体となる。 -/
lemma tracedSignedLoopUnitComparison_restriction (n : ℕ) :
    (X.sigma n).right ▷ (Δ[1] : SSet.{u}) ≫
      (tracedSignedLoopUnitComparison X (n + 1)).homotopy.h =
    (KanSequence.tracedRectificationComposite (X := X.toKanSequence)
      (Y := KanSequence.signedLoopTail X.toKanSequence) (KanSequence.kanAdjoint X.toKanSequence)
      (signedLoopUnitStructurePath X) n
      (KanSequence.tracedRectificationStage (X := X.toKanSequence)
        (Y := KanSequence.signedLoopTail X.toKanSequence) X.sigma_mono
        (KanSequence.kanAdjoint X.toKanSequence)
        (signedLoopUnitStructurePath X) n)).path.homotopy.h := by
  rw [tracedSignedLoopUnitComparison, tracedRectifyIntoComparison,
    PointedMapping.VerticalPath.changeEndpoints_homotopy_h]
  exact KanSequence.tracedRectifyComparison_restriction (X := X.toKanSequence)
    (Y := KanSequence.signedLoopTail X.toKanSequence) X.sigma_mono
    (KanSequence.kanAdjoint X.toKanSequence) (signedLoopUnitStructurePath X) n

/-- トレースを保持した単位も全段・全基点で π 同型。 -/
lemma tracedSignedLoopUnit_levelwise (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((tracedSignedLoopUnit X).app n).right :=
  tracedRectifyInto_levelwise X (KanSequence.signedLoopTail X.toKanSequence)
    (KanSequence.signedLoopTail_omegaCondition X.toKanSequence_omega)
    (KanSequence.kanAdjoint X.toKanSequence) (signedLoopUnitStructurePath X)
    (KanSequence.kanAdjoint_piIsomorphism X.toKanSequence_omega) n

/-- 零段も元の Kan 随伴のままで、置換射影後の厳密な始点を保つ。 -/
lemma tracedSignedLoopUnit_projection_zero :
    (tracedSignedLoopUnit X).app 0 ≫ (signedLoopProjection X).app 0 =
      KanSequence.kanAdjoint X.toKanSequence 0 := by
  rw [tracedSignedLoopUnit_projection]
  rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum
