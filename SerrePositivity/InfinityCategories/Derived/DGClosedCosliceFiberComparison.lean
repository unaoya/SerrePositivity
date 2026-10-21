module
public import SerrePositivity.InfinityCategories.Derived.DGClosedCosliceLinearCoordinates
/-!
概要：同じ実 coslice fiber の閉前合成を、左 Hom の同じ鎖写像作用へ厳密に同定する。
方針：全線形座標の単射性で全写像を照合し、準同型不変性を実 fiber 射へ戻す。
規約：対象の小ささも前三角性も不要。使われ方：Hom 関手族の実 fiber 同値の判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
  (x q y : D) (s : ForgetEnrichment.of (Complex R) q ⟶ ForgetEnrichment.of (Complex R) x)
/-- 実 fiber の左 Hom 表示は、同じ標準 Hom 前合成鎖写像の作用に等しい。 -/
lemma dgCoslicePrecomposeLeftMap_eq_chainMap :
    dgCoslicePrecomposeLeftMap R D x q y s =
      dgLeftPinchedChainMap R D D
        (eHomWhiskerRight (Complex R) s (ForgetEnrichment.of (Complex R) y)) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro t
  apply (dgLeftPinchedLinearEquiv R D q y n).injective
  exact (dgCoslicePrecomposeLeftMap_linear R D x q y s t).trans
    (dgLeftPinchedChainMap_linear R D D _ t).symm
lemma dgCoslicePrecomposeLeftMap_isQCatEquivalence
    [QuasiIso (eHomWhiskerRight (Complex R) s (ForgetEnrichment.of (Complex R) y))] :
    IsQCatEquivalence (dgCoslicePrecomposeLeftMap R D x q y s) := by
  rw [dgCoslicePrecomposeLeftMap_eq_chainMap]
  exact dgLeftPinchedChainMap_isQCatEquivalence R D D _
lemma dgCoslicePrecomposeFiber_isQCatEquivalence
    [QuasiIso (eHomWhiskerRight (Complex R) s (ForgetEnrichment.of (Complex R) y))] :
    IsQCatEquivalence (dgCoslicePrecomposeFiber R D x q y s) := by
  let e := pinchedLeftCosliceFiberIso (X := dgNerve R D)
    (Simplex.vertex (A := R) x) (Simplex.vertex y)
  let f := pinchedLeftCosliceFiberIso (X := dgNerve R D)
    (Simplex.vertex (A := R) q) (Simplex.vertex y)
  have H := dgCoslicePrecomposeLeftMap_isQCatEquivalence R D x q y s
  change IsQCatEquivalence (e.hom ≫ (dgCoslicePrecomposeFiber R D x q y s ≫ f.inv)) at H
  exact (qCatEquivalenceOfIso f.symm).isQCatEquivalence.cancel_right
    ((qCatEquivalenceOfIso e).isQCatEquivalence.cancel_left H)
end SerrePositivity.InfinityCategories
