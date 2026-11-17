module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleGlobalAugmentation

/-!
概要：同じ基底からのタプル増大は、同じ nerve 項の大域切断を経由する。
方針：元のスカラーの係数写像と恒等スカラーの増大を同じ零次成分で照合する。
規約：元の基底の環、増大射、Frobenius 係数、タプルを保持する。
使われ方：環の conerve から同じ二重 Čech への増大を含む比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Opposite
universe u
variable {R : Type u} [CommRing R] {Y : Scheme.{u}}
variable (f : Y ⟶ Spec (CommRingCat.of R)) {ι : Type} [Fintype ι] [DecidableEq ι]
variable (U : ι → Y.Opens) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)

set_option backward.isDefEq.respectTransparency false in
/-- 元の基底からの同じ増大は、実際の大域スカラーと同じ恒等スカラーの増大の合成。 -/
theorem schemePerfectCechTupleAugmentationHom_factor_global (n : SimplexCategory) :
    schemePerfectCechTupleAugmentationHom f U p hp hR n =
      (HomologicalComplex.single (ModuleCat.{u} ℤ) (ComplexShape.up ℕ) 0).map
        (ModuleCat.ofHom (frobeniusDirectLimitMap p hp hR
          (schemeCechNervePresheaf_primeCast f p hR (op n) (op ⊤))
          (schemeScalarHom _ ((Arrow.mk f).augmentedCechNerve.hom.app (op n)))).toAddMonoidHom.toIntLinearMap) ≫
        schemePerfectCechTupleGlobalAugmentationHom f U p hp
          (schemeCechNervePresheaf_primeCast f p hR) n := by
  letI := cechFiniteIndexOrder (Fin (n.len + 1) → ι)
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, schemePerfectCechTupleAugmentationHom_f_zero,
    schemePerfectCechTupleGlobalAugmentationHom_f_zero, HomologicalComplex.single_map_f_self]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  congr 1
  apply ModuleCat.hom_ext
  change schemeStructurePerfectCechAugmentation
      ((Arrow.mk f).cechNerve.obj (op n))
      (schemeScalarHom _ ((Arrow.mk f).augmentedCechNerve.hom.app (op n))) p hp hR
      (schemeCechNervePresheaf_primeCast f p hR (op n))
      (schemeCechTupleOpen f U (op n)) =
    (schemeStructurePerfectCechAugmentation ((Arrow.mk f).cechNerve.obj (op n))
      (RingHom.id _) p hp (schemeCechNervePresheaf_primeCast f p hR (op n) (op ⊤))
      (schemeCechNervePresheaf_primeCast f p hR (op n))
      (schemeCechTupleOpen f U (op n))).comp _
  rw [schemeStructurePerfectCechAugmentation_id]
  rfl

end SerrePositivity.AlgebraicGeometry
