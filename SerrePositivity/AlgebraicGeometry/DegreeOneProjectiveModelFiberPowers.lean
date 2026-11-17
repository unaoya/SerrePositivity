module

public import SerrePositivity.AlgebraicGeometry.DegreeOneProjectiveModelPullback
public import SerrePositivity.AlgebraicGeometry.FiniteFiberPowerUnit
public import Mathlib.AlgebraicTopology.CechNerve

/-!
概要：有限な次数一表示を、既存の Čech nerve の各正の有限ファイバー冪へ渡す。
方針：一個の冪の同型と、実際の pullback の表示の合成則で帰納する。
規約：既存の wide pullback と、元の増大項への射を保つ。
使われ方：射影版の Čech の四角形を有限ファイバー冪に適用する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits Opposite
universe u
variable {R : Type u} [CommRing R] {X : Scheme.{u}}
variable {f : X ⟶ Spec (CommRingCat.of R)}

/-- 既存の n+1 個のファイバー冪の base は、同じ基底上の次数一表示を持つ。 -/
def DegreeOneProjectiveModel.finiteFiberPower (m : DegreeOneProjectiveModel f) (n : ℕ) :
    DegreeOneProjectiveModel (WidePullback.base (fun _ : Fin (n + 1) ↦ f)) := by
  induction n with
  | zero =>
    exact (finiteFiberPowerZeroIso_hom_base f) ▸ m.ofIso (finiteFiberPowerZeroIso f)
  | succ n ih =>
    let h := isPullback_finiteFiberPowerSucc f n
    have hb : h.isoPullback.hom ≫
        (Limits.pullback.fst (WidePullback.base (fun _ : Fin (n + 1) ↦ f)) f ≫
          WidePullback.base (fun _ : Fin (n + 1) ↦ f)) =
        WidePullback.base (fun _ : Fin (n + 1 + 1) ↦ f) := by
      rw [← Category.assoc, h.isoPullback_hom_fst]
      simp only [WidePullback.lift_base]
    exact hb ▸ (ih.pullback m).ofIso h.isoPullback

/-- 既存の増大 Čech nerve の n 次の射そのものの、同じ基底上の表示。 -/
def DegreeOneProjectiveModel.cechTerm (m : DegreeOneProjectiveModel f)
    (n : SimplexCategoryᵒᵖ) :
    DegreeOneProjectiveModel ((Arrow.mk f).augmentedCechNerve.hom.app n) :=
  m.finiteFiberPower n.unop.len

end SerrePositivity.AlgebraicGeometry
