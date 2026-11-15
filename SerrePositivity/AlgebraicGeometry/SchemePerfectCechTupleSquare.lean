module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechRefinedSquare
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleScalarPullback

/-!
概要：同じ nerve の実際の係数と増大軸を、既存の四角形へ渡す。
方針：実際の mapCechNerve と同じ被覆の逆像の等式に沿って代入する。
規約：元の係数関手・スカラー・商・引き戻しを保持する。
使われ方：F8 の全複体を同じ可換な nerve の図式へ渡す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {R S : Type u} [CommRing R] [CommRing S] {X Y : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ Spec (CommRingCat.of R))
variable (F : Arrow.mk f ⟶ Arrow.mk g) (q : R →+* S)
variable (hq : F.right = Spec.map (CommRingCat.ofHom q))
variable {ι : Type} [Fintype ι] [DecidableEq ι] (U : ι → Y.Opens)
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hS : (p : S) = 0)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ nerve の実際の係数とスカラーを、既存の増大四角形へ代入した値。 -/
def schemePerfectCechTupleSquare (n : SimplexCategory) : CechAugmentedSquare.{u} ℤ := by
  letI := cechFiniteIndexOrder (Fin (n.len + 1) → ι)
  exact schemeStructurePerfectCechRefinedSquare ((Arrow.mapCechNerve F).app (op n)) q
    (schemeScalarHom _ ((Arrow.mk g).augmentedCechNerve.hom.app (op n)))
    (schemeScalarHom _ ((Arrow.mk f).augmentedCechNerve.hom.app (op n)))
    (schemeCechNerveMapScalarHom_naturality f g F q hq (op n)) p hp hR hS
    (schemeCechNervePresheaf_primeCast g p hR (op n))
    (schemeCechNervePresheaf_primeCast f p hS (op n))
    (schemeCechTupleOpen g U (op n))
    (schemeCechTupleOpen f (fun i ↦ F.left ⁻¹ᵁ U i) (op n)) id
    (fun t ↦ le_of_eq (schemeCechTupleOpen_mapCechNerve_preimage F U (op n) t))

/-- 同じ四角形の左複体は、元の実際の係数関手の複体。 -/
theorem schemePerfectCechTupleSquare_C (n : SimplexCategory) :
    (schemePerfectCechTupleSquare f g F q hq U p hp hR hS n).C =
      schemePerfectCechTupleComplex g U p hp (schemeCechNervePresheaf_primeCast g p hR) n := rfl

/-- 同じ四角形の右複体は、元の逆像被覆の実際の係数関手の複体。 -/
theorem schemePerfectCechTupleSquare_E (n : SimplexCategory) :
    (schemePerfectCechTupleSquare f g F q hq U p hp hR hS n).E =
      schemePerfectCechTupleComplex f (fun i ↦ F.left ⁻¹ᵁ U i) p hp
        (schemeCechNervePresheaf_primeCast f p hS) n := rfl

/-- 同じ四角形の制限は、実際の係数関手の引き戻しそのもの。 -/
theorem schemePerfectCechTupleSquare_restriction (n : SimplexCategory) :
    (schemePerfectCechTupleSquare f g F q hq U p hp hR hS n).restriction =
      schemePerfectCechTuplePullbackMap F U p hp (schemeCechNervePresheaf_primeCast f p hS)
        (schemeCechNervePresheaf_primeCast g p hR) n := rfl

/-- 同じ四角形のスカラーは、同じ基底からの実際の増大写像。 -/
theorem schemePerfectCechTupleSquare_scalar (n : SimplexCategory) :
    (schemePerfectCechTupleSquare f g F q hq U p hp hR hS n).scalar =
      schemePerfectCechTupleAugmentation g U p hp hR n := rfl

/-- 同じ四角形の商の辺は、元の Frobenius の係数写像。 -/
theorem schemePerfectCechTupleSquare_quotient (n : SimplexCategory) :
    (schemePerfectCechTupleSquare f g F q hq U p hp hR hS n).quotient =
      (frobeniusDirectLimitMap p hp hR hS q).toAddMonoidHom.toIntLinearMap := rfl

/-- 同じ四角形の中心は、同じ商の基底からの実際の増大写像。 -/
theorem schemePerfectCechTupleSquare_center (n : SimplexCategory) :
    (schemePerfectCechTupleSquare f g F q hq U p hp hR hS n).center =
      schemePerfectCechTupleAugmentation f (fun i ↦ F.left ⁻¹ᵁ U i) p hp hS n := rfl

end SerrePositivity.AlgebraicGeometry
