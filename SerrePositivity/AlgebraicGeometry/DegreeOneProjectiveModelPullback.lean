module

public import SerrePositivity.AlgebraicGeometry.DegreeOneProjectiveModel
public import SerrePositivity.AlgebraicGeometry.SegreProjectivePullback
public import SerrePositivity.AlgebraicGeometry.SegreProjectiveStructureMap
public import Mathlib.Data.Fintype.EquivFin

/-!
概要：二つの有限な次数一表示を、実際のファイバー積の表示へ合成する。
方針：既存の Segre 座標環と Cartesian 四角形を元の二つの同型で移送する。
規約：元の基底への射と全射評価を保持し、追加の平坦性を仮定しない。
使われ方：Čech nerve の有限ファイバー冪の射影表示。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

set_option backward.isDefEq.respectTransparency false in
/-- 実際の同じ基底上の pullback は、元の二つの次数一表示を合成した表示を持つ。 -/
def DegreeOneProjectiveModel.pullback {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of R)} {g : Y ⟶ Spec (CommRingCat.of R)}
    (m : DegreeOneProjectiveModel f) (n : DegreeOneProjectiveModel g) :
    DegreeOneProjectiveModel (Limits.pullback.fst f g ≫ f) := by
  letI : LinearOrder (m.index × n.index) :=
    LinearOrder.lift' (Fintype.equivFin (m.index × n.index)) (Fintype.equivFin _).injective
  let SG := segreCoordinateGrade (R := R) m.generator n.generator
  letI := segreCoordinateGradedRing m.generator n.generator m.grade m.homogeneous
  let z : m.index × n.index → SegreCoordinateRing (R := R) m.generator n.generator :=
    fun p ↦ segreCoordinateProjection m.generator n.generator (MvPolynomial.X p)
  have hz : ∀ p, z p ∈ SG 1 := fun p ↦
    segreCoordinate_denominator_mem m.generator n.generator p.1 p.2
  have hs : Function.Surjective (MvPolynomial.aeval (R := R) z) := by
    change Function.Surjective (MvPolynomial.aeval (R := R) (fun p : m.index × n.index ↦
      segreCoordinateProjection m.generator n.generator (MvPolynomial.X p)))
    rw [segreCoordinate_aeval]
    exact segreCoordinateProjection_surjective m.generator n.generator
  let l := segreLeftProjection m.generator n.generator m.grade m.homogeneous m.surjective
  let r := segreRightProjection m.generator n.generator m.grade m.homogeneous
    n.grade n.homogeneous n.surjective
  have hm : m.iso.inv ≫ f = projectiveCechStructureMap m.grade :=
    (m.iso.inv_comp_eq).mpr m.over.symm
  have hn : n.iso.inv ≫ g = projectiveCechStructureMap n.grade :=
    (n.iso.inv_comp_eq).mpr n.over.symm
  have hP : IsPullback (l ≫ m.iso.inv) (r ≫ n.iso.inv) f g := by
    refine (isPullback_segreProjectiveProjections m.generator n.generator m.grade m.homogeneous
      n.grade n.homogeneous m.surjective n.surjective).of_iso
      (Iso.refl _) m.iso.symm n.iso.symm (Iso.refl _) (by simp [l]) (by simp [r]) ?_ ?_
    · simpa only [Iso.refl_hom, Category.comp_id, Iso.symm_hom] using hm.symm
    · simpa only [Iso.refl_hom, Category.comp_id, Iso.symm_hom] using hn.symm
  have hl : (l ≫ m.iso.inv) ≫ f = projectiveCechStructureMap SG := by
    rw [Category.assoc, hm]
    exact segreLeftProjection_structureMap m.generator n.generator m.grade
      m.homogeneous m.surjective
  have hbase : hP.isoPullback.inv ≫ projectiveCechStructureMap SG =
      Limits.pullback.fst f g ≫ f := by
    rw [← hl, ← Category.assoc, hP.isoPullback_inv_fst]
  exact hbase ▸ (degreeOneProjectiveModelOfProj SG z hz hs).ofIso hP.isoPullback.symm

end SerrePositivity.AlgebraicGeometry
