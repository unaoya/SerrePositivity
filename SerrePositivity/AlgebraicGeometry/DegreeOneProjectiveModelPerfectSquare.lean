module

public import SerrePositivity.AlgebraicGeometry.DegreeOneProjectiveModelScalar
public import SerrePositivity.AlgebraicGeometry.DegreeOneProjectiveModelCechData
public import SerrePositivity.AlgebraicGeometry.ProjectivePerfectCartesianAffineCover
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechSquareIsoComparison

/-!
概要：射影版 F8 の完全性を、実際の表示と同じ閉中心の四角形へ戻す。
方針：逆同型で同じ被覆を移し、実際の三角形の四角形比較で戻す。
規約：有限性・標数・全射性・中心外同型は元の表示と射から供給する。
使われ方：実際のブローアップの有限ファイバー冪の降下。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {X Y : Scheme.{u}} {f : Y ⟶ Spec (CommRingCat.of R)}

set_option backward.isDefEq.respectTransparency false in
/-- 同じ閉中心と実際の構造射の射影表示での F8 の完全性。
BST13 Lemma 3.9・BS17 Lemma 4.6(i) に使う Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する
（Stacks 30.2.6）が、この比較は形式化しない。 -/
theorem DegreeOneProjectiveModel.perfectCartesianSquare_acyclic
    (m : DegreeOneProjectiveModel f) (I : Ideal R)
    (g : X ⟶ Y) (iX : X ⟶ Spec (CommRingCat.of (R ⧸ I ^ 1)))
    (H : IsPullback g iX f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ 1)))))
    [Surjective f] [IsIso (f ∣_ affineCenterComplement I)]
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)
    {ι : Type} [LinearOrder ι] [Fintype ι] (V : ι → Y.Opens)
    (hV : ∀ i, IsAffineOpen (V i)) (hcV : (⨆ i, V i) = ⊤) :
    (schemeStructurePerfectCechSquare g (Ideal.Quotient.mk (I ^ 1))
      (schemeScalarHom Y f) (schemeScalarHom X iX)
      (schemeScalarHom_naturality Y g f iX (Ideal.Quotient.mk (I ^ 1)) H.w).symm
      p hp hR (frobeniusQuotientPrimeCast p hR (I ^ 1))
      (projectivePullbackPresheaf_primeCast m.grade m.iso.hom p hR)
      (projectivePullbackPresheaf_primeCast m.grade (g ≫ m.iso.hom) p hR) V).totalComplex.Acyclic := by
  letI := degreeOnePolynomialAlgebra (R := R) m.generator
  obtain ⟨ht, hg, hf, hspan⟩ := m.projectiveCechData
  letI := ht
  letI := hg
  letI := hf
  have : Surjective (schemeScalarMorphism (Proj m.grade)
      (projectiveScalarToGlobalSections m.grade)) := m.structure_surjective
  have : IsIso (schemeScalarMorphism (Proj m.grade)
      (projectiveScalarToGlobalSections m.grade) ∣_ affineCenterComplement I) :=
    m.restrict_isIso (affineCenterComplement I)
  have hA : (p : m.ring) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg (algebraMap R m.ring) hR
  let U : ι → (Proj m.grade).Opens := fun i ↦ m.iso.inv ⁻¹ᵁ V i
  have hU : ∀ i, IsAffineOpen (U i) := fun i ↦ (hV i).preimage m.iso.inv
  have hcU : (⨆ i, U i) = ⊤ := m.iso.inv.iSup_preimage_eq_top hcV
  have H' := m.cartesian g iX (Ideal.Quotient.mk (I ^ 1)) H
  have ha := projectivePerfectCartesianScalarSquare_acyclic m.grade I iX
    (g ≫ m.iso.hom) H' p hp hR hA hspan U hU hcU
  have hv : (fun i ↦ m.iso.hom ⁻¹ᵁ U i) = V := by
    funext i
    dsimp only [U]
    rw [← Scheme.Hom.comp_preimage, m.iso.hom_inv_id]
    simp
  have hc := schemeStructurePerfectCechSquare_iso_acyclic_iff m.iso.hom
    g (g ≫ m.iso.hom) rfl (Ideal.Quotient.mk (I ^ 1))
    (projectiveScalarToGlobalSections m.grade) (schemeScalarHom Y f) (schemeScalarHom X iX)
    m.scalarHom (projectivePerfectCartesianScalarCompatibility m.grade I iX
      (g ≫ m.iso.hom) H')
    (schemeScalarHom_naturality Y g f iX (Ideal.Quotient.mk (I ^ 1)) H.w).symm
    p hp hR (frobeniusQuotientPrimeCast p hR (I ^ 1))
    (projectiveProjPresheaf_primeCast m.grade p hR)
    (projectivePullbackPresheaf_primeCast m.grade m.iso.hom p hR)
    (projectivePullbackPresheaf_primeCast m.grade (g ≫ m.iso.hom) p hR) U
  have hh := hc.mp ha
  simpa only [hv] using hh

end SerrePositivity.AlgebraicGeometry
