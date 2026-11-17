module

public import SerrePositivity.AlgebraicGeometry.ReesFiniteFiberPowerModel
public import SerrePositivity.AlgebraicGeometry.BlowupOpenComparison

/-!
概要：一般の blowup のアフィン開への既存の比較から、同じ基底上の次数一表示を得る。
方針：開像の式で Cartesian 四角形を確認し、既存の Rees 表示の同型移送を使う。
規約：元の pullback.snd と既存の増大 Čech nerve を保つ。
使われ方：Noether 基底上の帰納をアフィン開で射影版の計算へ渡す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits Opposite
universe u
variable {X : Scheme.{u}} {A : CommRingCat.{u}} (j : Spec A ⟶ X) [IsOpenImmersion j]
variable (K : X.IdealSheafData)

/-- 既存のアフィン開の比較は、一般の blowup の同じ基底変更の Cartesian 四角形。 -/
theorem isPullback_blowupAffineOpenMap :
    IsPullback (blowupAffineOpenMap j K)
      (affineBlowupπ (specIdealEquiv A (K.comap j))) (blowupπ K) j := by
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback
  · exact blowupAffineOpenMap_base j K
  · apply TopologicalSpace.Opens.ext
    exact (blowupAffineOpenMap_range j K).symm

/-- アフィン開への実際の pullback の射は、同じ基底上の次数一表示を持つ。 -/
theorem nonempty_blowupAffinePullbackProjectiveModel
    (hK : (specIdealEquiv A (K.comap j)).FG) :
    Nonempty (DegreeOneProjectiveModel (R := A) (pullback.snd (blowupπ K) j)) := by
  obtain ⟨m⟩ := nonempty_affineBlowupDegreeOneProjectiveModel
    (specIdealEquiv A (K.comap j)) hK
  let h := isPullback_blowupAffineOpenMap j K
  exact ⟨h.isoPullback_inv_snd ▸ m.ofIso h.isoPullback.symm⟩

/-- 一般の blowup をアフィン開へ戻した既存の Čech nerve の各項の同じ表示。 -/
theorem nonempty_blowupAffinePullbackCechTermModel
    (hK : (specIdealEquiv A (K.comap j)).FG) (n : SimplexCategoryᵒᵖ) :
    Nonempty (DegreeOneProjectiveModel (R := A)
      ((Arrow.mk (pullback.snd (blowupπ K) j)).augmentedCechNerve.hom.app n)) := by
  obtain ⟨m⟩ := nonempty_blowupAffinePullbackProjectiveModel j K hK
  exact ⟨m.cechTerm n⟩

end SerrePositivity.AlgebraicGeometry
