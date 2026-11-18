module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechConstantNaturality
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleAugmented

/-!
概要：元のタプル被覆の実際の係数関手へ、全次数で同じ基底から増大する。
方針：実際の基底への射に沿う大域スカラーと、その全次数の自然性を使う。
規約：元のsingleの増大と同じ各次数の写像を保持する。
使われ方：定数増大列の全複体から元の増大された二重Čechへのretract。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {R : Type u} [CommRing R] {Y : Scheme.{u}}
variable (f : Y ⟶ Spec (CommRingCat.of R)) {ι : Type} [Fintype ι] [DecidableEq ι]
variable (U : ι → Y.Opens) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)

set_option backward.isDefEq.respectTransparency false in
/-- 元の各nerveの実際の大域スカラーによる、同じ全次数の増大。 -/
def schemePerfectCechTupleConstantAugmentation (n : SimplexCategory) :
    cechConstantComplex (ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR)) ⟶
      schemePerfectCechTupleComplex f U p hp (schemeCechNervePresheaf_primeCast f p hR) n := by
  letI := cechFiniteIndexOrder (Fin (n.len + 1) → ι)
  exact schemeStructurePerfectCechConstantAugmentation ((Arrow.mk f).cechNerve.obj (op n))
    (schemeScalarHom _ ((Arrow.mk f).augmentedCechNerve.hom.app (op n)))
    p hp hR (schemeCechNervePresheaf_primeCast f p hR (op n))
    (schemeCechTupleOpen f U (op n))

set_option backward.isDefEq.respectTransparency false in
/-- 元の同じタプルの前合成に、全次数の増大は自然。 -/
theorem schemePerfectCechTupleConstantAugmentation_naturality {m n : SimplexCategory}
    (a : m ⟶ n) :
    schemePerfectCechTupleConstantAugmentation f U p hp hR m ≫
        schemePerfectCechTupleMap f U p hp (schemeCechNervePresheaf_primeCast f p hR) a =
      schemePerfectCechTupleConstantAugmentation f U p hp hR n := by
  letI := cechFiniteIndexOrder (Fin (m.len + 1) → ι)
  letI := cechFiniteIndexOrder (Fin (n.len + 1) → ι)
  exact schemeStructurePerfectCechConstantAugmentation_naturality
    ((Arrow.mk f).cechNerve.map a.op)
    (schemeScalarHom _ ((Arrow.mk f).augmentedCechNerve.hom.app (op m)))
    (schemeScalarHom _ ((Arrow.mk f).augmentedCechNerve.hom.app (op n)))
    (schemeCechNerveScalarHom_naturality f a.op) p hp hR
    (schemeCechNervePresheaf_primeCast f p hR (op m))
    (schemeCechNervePresheaf_primeCast f p hR (op n))
    (schemeCechTupleOpen f U (op m)) (schemeCechTupleOpen f U (op n))
    (fun t j ↦ t (a.toOrderHom j)) (schemeCechTupleOpen_map_le f U a.op)

set_option backward.isDefEq.respectTransparency false in
/-- 元のsingleからの包含との合成は、既存の同じsingleの増大。 -/
theorem schemePerfectCechTupleConstantAugmentation_single (n : SimplexCategory) :
    cechConstantSingleAugmentation (ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR)) ≫
        schemePerfectCechTupleConstantAugmentation f U p hp hR n =
      schemePerfectCechTupleAugmentationHom f U p hp hR n := by
  letI := cechFiniteIndexOrder (Fin (n.len + 1) → ι)
  apply HomologicalComplex.from_single_hom_ext
  rw [schemePerfectCechTupleAugmentationHom_f_zero]
  exact schemeStructurePerfectCechConstantAugmentation_single_zero
    ((Arrow.mk f).cechNerve.obj (op n))
    (schemeScalarHom _ ((Arrow.mk f).augmentedCechNerve.hom.app (op n)))
    p hp hR (schemeCechNervePresheaf_primeCast f p hR (op n))
    (schemeCechTupleOpen f U (op n))

/-- 元のタプル被覆の係数関手への、同じ全次数の増大の自然変換。 -/
def schemePerfectCechTupleConstantAugmentationHom :
    (Functor.const SimplexCategory).obj
        (cechConstantComplex (ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR))) ⟶
      schemePerfectCechTupleFunctor f U p hp (schemeCechNervePresheaf_primeCast f p hR) where
  app := schemePerfectCechTupleConstantAugmentation f U p hp hR
  naturality {m n} a := by
    change 𝟙 _ ≫ schemePerfectCechTupleConstantAugmentation f U p hp hR n = _
    rw [Category.id_comp]
    exact (schemePerfectCechTupleConstantAugmentation_naturality f U p hp hR a).symm

set_option backward.isDefEq.respectTransparency false in
/-- 同じsingleの包含との合成は、元の増大図式の同じ自然変換。 -/
theorem schemePerfectCechTupleConstantAugmentationHom_single :
    (Functor.const SimplexCategory).map
        (cechConstantSingleAugmentation (ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR))) ≫
      schemePerfectCechTupleConstantAugmentationHom f U p hp hR =
        (schemePerfectCechTupleAugmented f U p hp hR).hom := by
  apply NatTrans.ext
  funext n
  exact schemePerfectCechTupleConstantAugmentation_single f U p hp hR n

end SerrePositivity.AlgebraicGeometry
