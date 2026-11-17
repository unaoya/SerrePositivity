module

public import SerrePositivity.AlgebraicGeometry.CechSingleAugmentationQuasiIso
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleGlobalAugmentation
public import SerrePositivity.AlgebraicGeometry.AffineCechNerveTupleExact

/-!
概要：アフィンな nerve の同じ大域増大は、同じタプル複体への準同型。
方針：既存の各列の完全性を、同じ single からの射に移す。
規約：元の射と全次数の自然性を持つ増大の Čech 版。
使われ方：環の conerve と実際の二重 Čech の各列の接続。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Opposite
universe u
variable {Y S : Scheme.{u}} (f : Y ⟶ S) [IsAffine Y] [IsAffine S]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (U : ι → Y.Opens)
variable (p : ℕ) (hp : p.Prime)
variable (h : ∀ n : SimplexCategoryᵒᵖ,
  ∀ O, (p : ((Arrow.mk f).cechNerve.obj n).presheaf.obj O) = 0)

set_option backward.isDefEq.respectTransparency false in
/-- 同じアフィン nerve 項の実際の大域増大は、各次数で準同型。
Stacks 30.2.6 に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem affineCechNerveTupleGlobalAugmentation_quasiIsoAt
    (hU : ∀ i, IsAffineOpen (U i)) (hcU : (⨆ i, U i) = ⊤)
    (n : SimplexCategory) (q : ℕ) :
    QuasiIsoAt (schemePerfectCechTupleGlobalAugmentationHom f U p hp h n) q := by
  letI := cechFiniteIndexOrder (Fin (n.len + 1) → ι)
  let A := ModuleCat.of ℤ (FrobeniusDirectLimit
    Γ((Arrow.mk f).cechNerve.obj (op n), ⊤) p hp (h (op n) (op ⊤)))
  let C := schemePerfectCechTupleComplex f U p hp h n
  let ε : A ⟶ C.X 0 := ModuleCat.ofHom (schemeStructurePerfectCechAugmentation
    ((Arrow.mk f).cechNerve.obj (op n)) (RingHom.id _) p hp (h (op n) (op ⊤))
    (h (op n)) (schemeCechTupleOpen f U (op n)))
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 A
  have he : (schemePerfectCechTupleGlobalAugmentationHom f U p hp h n).f 0 =
      e.hom ≫ ε := schemePerfectCechTupleGlobalAugmentationHom_f_zero f U p hp h n
  apply cechSingleAugmentation_quasiIsoAt A C
    (schemePerfectCechTupleGlobalAugmentationHom f U p hp h n) ?_ ?_ ?_ q
  · rw [he]
    change Function.Injective (ε.hom.comp e.hom.hom)
    exact (affineCechNerveTuple_augmentation_injective f U p hp h hU hcU n).comp
      ((ModuleCat.mono_iff_injective e.hom).mp inferInstance)
  · rw [he]
    change Function.Exact (ε.hom.comp e.hom.hom) (C.d 0 1).hom
    apply ((ModuleCat.epi_iff_surjective e.hom).mp inferInstance).comp_exact_iff_exact.mpr
    exact affineCechNerveTuple_augmentation_exact f U p hp h hU hcU n
  · intro k
    rw [C.exactAt_iff' k (k + 1) (k + 2) (by simp) (by simp)]
    apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    change Function.Exact (C.d k (k + 1)).hom (C.d (k + 1) ((k + 1) + 1)).hom
    simpa only [C, schemePerfectCechTupleComplex, fullCechComplex,
      CochainComplex.of_d, ModuleCat.hom_ofHom] using
      (affineCechNerveTuple_augmentedExact f U p hp h hU hcU n).2 (k + 1)

/-- 同じ自然な大域増大の各成分は、同じタプル複体への準同型。 -/
theorem affineCechNerveTupleGlobalAugmentation_quasiIso
    (hU : ∀ i, IsAffineOpen (U i)) (hcU : (⨆ i, U i) = ⊤) (n : SimplexCategory) :
    QuasiIso (schemePerfectCechTupleGlobalAugmentationHom f U p hp h n) :=
  ⟨affineCechNerveTupleGlobalAugmentation_quasiIsoAt f U p hp h hU hcU n⟩

end SerrePositivity.AlgebraicGeometry
