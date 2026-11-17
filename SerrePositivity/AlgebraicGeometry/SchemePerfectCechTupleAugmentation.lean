module

public import SerrePositivity.AlgebraicGeometry.SchemeCechNerveScalars
public import SerrePositivity.AlgebraicGeometry.CechFiniteIndexOrder
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleFunctor
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechRefinedAugmentation

/-!
概要：同じ nerve の実際の大域スカラーを、同じタプル複体の増大写像にする。
方針：基底への射の自然性と、既存の増大写像の引き戻しの法則を使う。
規約：標数は元の基底から供給し、等号判定と実際の引き戻しを保つ。
使われ方：増大軸を含む可換な二重 Čech の係数図式。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {R : Type u} [CommRing R] {Y : Scheme.{u}}
variable (f : Y ⟶ Spec (CommRingCat.of R)) {ι : Type} [Fintype ι] [DecidableEq ι]
variable (U : ι → Y.Opens) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ実際の基底への射に沿う、同じタプル複体の増大写像。 -/
def schemePerfectCechTupleAugmentation (n : SimplexCategory) :
    FrobeniusDirectLimit R p hp hR →ₗ[ℤ]
      (schemePerfectCechTupleComplex f U p hp
        (schemeCechNervePresheaf_primeCast f p hR) n).X 0 := by
  letI := cechFiniteIndexOrder (Fin (n.len + 1) → ι)
  exact schemeStructurePerfectCechAugmentation ((Arrow.mk f).cechNerve.obj (op n))
    (schemeScalarHom _ ((Arrow.mk f).augmentedCechNerve.hom.app (op n)))
    p hp hR (schemeCechNervePresheaf_primeCast f p hR (op n))
    (schemeCechTupleOpen f U (op n))

set_option backward.isDefEq.respectTransparency false in
/-- 同じ増大写像は、実際のタプル複体のサイクルに入る。 -/
theorem schemePerfectCechTupleAugmentation_cycle (n : SimplexCategory) :
    ((schemePerfectCechTupleComplex f U p hp
      (schemeCechNervePresheaf_primeCast f p hR) n).d 0 1).hom.comp
      (schemePerfectCechTupleAugmentation f U p hp hR n) = 0 := by
  letI := cechFiniteIndexOrder (Fin (n.len + 1) → ι)
  exact schemeStructurePerfectCechAugmentation_cycle ((Arrow.mk f).cechNerve.obj (op n))
    (schemeScalarHom _ ((Arrow.mk f).augmentedCechNerve.hom.app (op n)))
    p hp hR (schemeCechNervePresheaf_primeCast f p hR (op n))
    (schemeCechTupleOpen f U (op n))

set_option backward.isDefEq.respectTransparency false in
/-- 同じ実際の増大写像は、全ての nerve の射に沿う引き戻しに自然。 -/
theorem schemePerfectCechTupleAugmentation_naturality {m n : SimplexCategory} (a : m ⟶ n) :
    ((schemePerfectCechTupleMap f U p hp
      (schemeCechNervePresheaf_primeCast f p hR) a).f 0).hom.comp
        (schemePerfectCechTupleAugmentation f U p hp hR m) =
      schemePerfectCechTupleAugmentation f U p hp hR n := by
  letI := cechFiniteIndexOrder (Fin (m.len + 1) → ι)
  letI := cechFiniteIndexOrder (Fin (n.len + 1) → ι)
  exact schemeStructurePerfectCechRefinedPullbackMap_augmentation
    ((Arrow.mk f).cechNerve.map a.op)
    (schemeScalarHom _ ((Arrow.mk f).augmentedCechNerve.hom.app (op m)))
    (schemeScalarHom _ ((Arrow.mk f).augmentedCechNerve.hom.app (op n)))
    (schemeCechNerveScalarHom_naturality f a.op) p hp hR
    (schemeCechNervePresheaf_primeCast f p hR (op m))
    (schemeCechNervePresheaf_primeCast f p hR (op n))
    (schemeCechTupleOpen f U (op m)) (schemeCechTupleOpen f U (op n))
    (fun t j ↦ t (a.toOrderHom j)) (schemeCechTupleOpen_map_le f U a.op)

end SerrePositivity.AlgebraicGeometry
