module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleConstantAugmentation
public import SerrePositivity.AlgebraicGeometry.CechConstantAugmentedDouble
public import SerrePositivity.AlgebraicGeometry.RectangularPerfectRowFunctor

/-!
概要：元の矩形の行に、同じ全次数の基底の増大を付ける。
方針：元の定数増大図式を、同じ縦次数の評価関手に通す。
規約：同じ基底とタプル被覆・全ての水平の写像を保持する。
使われ方：有限交叉族のアフィン射の完全性を元の行へ渡す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {R : Type u} [CommRing R] {Y : Scheme.{u}}
variable (f : Y ⟶ Spec (CommRingCat.of R)) {ι : Type} [Fintype ι] [DecidableEq ι]
variable (U : ι → Y.Opens) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (k : ℕ)

/-- 元の定数増大図式の同じ縦次数での評価。 -/
def rectangularPerfectAugmentedRow : CosimplicialObject.Augmented (ModuleCat.{u} ℤ) :=
  (CosimplicialObject.Augmented.whiskeringObj _ _
    (HomologicalComplex.eval (ModuleCat.{u} ℤ) (.up ℕ) k)).obj
      (cechConstantAugmentedObject (ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR))
        (schemePerfectCechTupleFunctor f U p hp (schemeCechNervePresheaf_primeCast f p hR))
        (schemePerfectCechTupleConstantAugmentationHom f U p hp hR))

/-- 同じ増大行の基底項は、元の基底環の同じFrobenius順極限。 -/
theorem rectangularPerfectAugmentedRow_left :
    (rectangularPerfectAugmentedRow f U p hp hR k).left =
      ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR) := rfl

/-- 同じ増大行の右の関手は、元の矩形の行の係数関手。 -/
theorem rectangularPerfectAugmentedRow_right :
    (rectangularPerfectAugmentedRow f U p hp hR k).right =
      rectangularPerfectRowFunctor f U p hp (schemeCechNervePresheaf_primeCast f p hR) k := rfl

set_option backward.isDefEq.respectTransparency false in
/-- 元の増大行の各タプルでの値は、同じ大域スカラーと実際の制限の合成。 -/
theorem rectangularPerfectAugmentedRow_hom_app_apply (n : SimplexCategory)
    (x : FrobeniusDirectLimit R p hp hR) (q : Fin (k + 1) → Fin (n.len + 1) → ι) :
    (((rectangularPerfectAugmentedRow f U p hp hR k).hom.app n).hom x) q =
      frobeniusDirectLimitMap p hp hR
        (schemeCechNervePresheaf_primeCast f p hR (op n)
          (op (cechOpenIntersection (schemeCechTupleOpen f U (op n)) (cechTupleSupport q))))
        ((((Arrow.mk f).cechNerve.obj (op n)).presheaf.map
          (homOfLE (show cechOpenIntersection (schemeCechTupleOpen f U (op n))
            (cechTupleSupport q) ≤ ⊤ from le_top)).op).hom.comp
          (schemeScalarHom _ ((Arrow.mk f).augmentedCechNerve.hom.app (op n)))) x := by
  letI := cechFiniteIndexOrder (Fin (n.len + 1) → ι)
  exact schemeStructurePerfectCechConstantAugmentation_apply
    ((Arrow.mk f).cechNerve.obj (op n))
    (schemeScalarHom _ ((Arrow.mk f).augmentedCechNerve.hom.app (op n)))
    p hp hR (schemeCechNervePresheaf_primeCast f p hR (op n))
    (schemeCechTupleOpen f U (op n)) k x q

end SerrePositivity.AlgebraicGeometry
