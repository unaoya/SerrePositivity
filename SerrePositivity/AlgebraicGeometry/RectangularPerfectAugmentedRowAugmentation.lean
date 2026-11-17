module

public import SerrePositivity.AlgebraicGeometry.RectangularPerfectAugmentedRow
public import SerrePositivity.AlgebraicGeometry.RectangularPerfectRowAugmentation
public import SerrePositivity.AlgebraicGeometry.SchemeScalarPerfectRestriction

/-!
概要：同じ矩形の行の係数同型が、元の基底の増大を保つことを評価で示す。
方針：元のΓの増大の評価とΓ–Specによる同じ係数移送を合成する。
規約：同じ元のappLE・Γ・タプル被覆を保持する。
使われ方：増大行の同型の可換性を、関手の同型の構成から分割する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
variable {R : Type u} [CommRing R] {Y : Scheme.{u}}
variable (f : Y ⟶ Spec (CommRingCat.of R)) {ι : Type} [Fintype ι] [DecidableEq ι]
variable (U : ι → Y.Opens) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (k : ℕ)
variable (hS : (p : Γ(Spec (CommRingCat.of R), ⊤)) = 0)
variable (hN : ∀ n : SimplexCategory, (p : (rectangularPerfectRowGammaFunctor f U k).obj n) = 0)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ矩形の行の比較は、Γ–Specで基底を戻した元の増大を保つ。 -/
theorem rectangularPerfectAugmentedRow_augmentation (n : SimplexCategory)
    (z : FrobeniusDirectLimit Γ(Spec (CommRingCat.of R), ⊤) p hp hS)
    (q : Fin (k + 1) → Fin (n.len + 1) → ι) :
    (((rectangularPerfectAugmentedRow f U p hp hR k).hom.app n).hom
      (frobeniusDirectLimitMap p hp hS hR (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom z)) q =
      rectangularPerfectRowEquiv f U p hp n k (hN n)
        (fun q ↦ schemeCechNervePresheaf_primeCast f p hR (op n)
          (op (cechOpenIntersection (schemeCechTupleOpen f U (op n)) (cechTupleSupport q))))
        (frobeniusDirectLimitMap p hp hS (hN n)
          (Scheme.Γ.map ((Arrow.mk (Sigma.desc
            (fun b : Fin (k + 1) → ι ↦ (⨅ r, U (b r)).ι ≫ f))).augmentedCechNerve.hom.app
              (op n)).op).hom z) q := by
  rw [rectangularPerfectAugmentedRow_hom_app_apply]
  have hs := schemeScalarPerfectRestriction_cancel
    ((Arrow.mk f).augmentedCechNerve.hom.app (op n))
    (cechOpenIntersection (schemeCechTupleOpen f U (op n)) (cechTupleSupport q))
    p hp hR hS (schemeCechNervePresheaf_primeCast f p hR (op n)
      (op (cechOpenIntersection (schemeCechTupleOpen f U (op n)) (cechTupleSupport q)))) z
  have hr := rectangularPerfectRowEquiv_augmentation f U p hp hS n k (hN n)
    (fun q ↦ schemeCechNervePresheaf_primeCast f p hR (op n)
      (op (cechOpenIntersection (schemeCechTupleOpen f U (op n)) (cechTupleSupport q)))) z q
  exact hs.trans hr.symm

end SerrePositivity.AlgebraicGeometry
