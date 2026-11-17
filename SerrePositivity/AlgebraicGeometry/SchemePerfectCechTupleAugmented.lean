module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleAugmentation
public import Mathlib.Algebra.Homology.Single

/-!
概要：実際の増大写像を、同じ係数の複体の増大余単体図式へ渡す。
方針：既存の single からの射の構成と、その零次成分の外延性を使う。
規約：元の増大写像と全ての nerve の写像を保つ。
使われ方：同じ四角形の基底・中心の増大軸の自然性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {R : Type u} [CommRing R] {Y : Scheme.{u}}
variable (f : Y ⟶ Spec (CommRingCat.of R)) {ι : Type} [Fintype ι] [DecidableEq ι]
variable (U : ι → Y.Opens) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ実際の増大写像を、既存の次数零 single からの複体の射にする。 -/
def schemePerfectCechTupleAugmentationHom (n : SimplexCategory) :
    (HomologicalComplex.single (ModuleCat.{u} ℤ) (ComplexShape.up ℕ) 0).obj
      (ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR)) ⟶
      schemePerfectCechTupleComplex f U p hp (schemeCechNervePresheaf_primeCast f p hR) n :=
  HomologicalComplex.mkHomFromSingle
    (ModuleCat.ofHom (schemePerfectCechTupleAugmentation f U p hp hR n)) (by
      intro k hk
      have he : k = 1 := Eq.symm hk
      clear hk
      subst k
      apply ModuleCat.hom_ext
      simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_zero] using
        schemePerfectCechTupleAugmentation_cycle f U p hp hR n)

/-- single からの射の零次成分は、同じ実際の増大写像。 -/
theorem schemePerfectCechTupleAugmentationHom_f_zero (n : SimplexCategory) :
    (schemePerfectCechTupleAugmentationHom f U p hp hR n).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
        (ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR))).hom ≫
        ModuleCat.ofHom (schemePerfectCechTupleAugmentation f U p hp hR n) :=
  HomologicalComplex.mkHomFromSingle_f _ _

set_option backward.isDefEq.respectTransparency false in
/-- 同じ single からの射は、実際の nerve の全ての射に自然。 -/
theorem schemePerfectCechTupleAugmentationHom_naturality {m n : SimplexCategory}
    (a : m ⟶ n) :
    schemePerfectCechTupleAugmentationHom f U p hp hR m ≫
        schemePerfectCechTupleMap f U p hp (schemeCechNervePresheaf_primeCast f p hR) a =
      schemePerfectCechTupleAugmentationHom f U p hp hR n := by
  apply HomologicalComplex.from_single_hom_ext
  have h0 : ModuleCat.ofHom (schemePerfectCechTupleAugmentation f U p hp hR m) ≫
      (schemePerfectCechTupleMap f U p hp
        (schemeCechNervePresheaf_primeCast f p hR) a).f 0 =
      ModuleCat.ofHom (schemePerfectCechTupleAugmentation f U p hp hR n) := by
    apply ModuleCat.hom_ext
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] using
      schemePerfectCechTupleAugmentation_naturality f U p hp hR a
  rw [HomologicalComplex.comp_f, schemePerfectCechTupleAugmentationHom_f_zero,
    schemePerfectCechTupleAugmentationHom_f_zero, Category.assoc, h0]

/-- 同じ R の増大項と実際のタプル複体の係数の増大余単体図式。 -/
def schemePerfectCechTupleAugmented :
    CosimplicialObject.Augmented (CochainComplex (ModuleCat.{u} ℤ) ℕ) where
  left := (HomologicalComplex.single (ModuleCat.{u} ℤ) (ComplexShape.up ℕ) 0).obj
    (ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR))
  right := schemePerfectCechTupleFunctor f U p hp (schemeCechNervePresheaf_primeCast f p hR)
  hom :=
    { app := schemePerfectCechTupleAugmentationHom f U p hp hR
      naturality := fun {m n} a ↦ by
        change 𝟙 _ ≫ schemePerfectCechTupleAugmentationHom f U p hp hR n =
          schemePerfectCechTupleAugmentationHom f U p hp hR m ≫
            schemePerfectCechTupleMap f U p hp (schemeCechNervePresheaf_primeCast f p hR) a
        rw [Category.id_comp]
        exact (schemePerfectCechTupleAugmentationHom_naturality f U p hp hR a).symm }

end SerrePositivity.AlgebraicGeometry
