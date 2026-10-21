module
public import SerrePositivity.InfinityCategories.Derived.DGFunctorClosedCosliceFiber
/-!
概要：実 coslice の合成比較の fiber 射を、同じ合成 Hom 鎖写像の左 Hom 作用へ同定する。
方針：後合成と閉前合成の全単体等式を結び、同じ鎖写像作用の厳密な合成則を使う。
規約：各因子の準同型性を要求せず、合成した同じ Hom 鎖写像の準同型性だけを使う。
使われ方：Hom 単位の実 coslice 比較が全 fiber で同値であることの証明。
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
variable (R : Type u) [CommRing R] {D E : Type v} [DGCategory R D] [DGCategory R E]
  (F : DGFunctor R D E) (x : D) (q : E) (y : D)
  (s : ForgetEnrichment.of (Complex R) q ⟶ ForgetEnrichment.of (Complex R) (F.obj x))
/-- 同じ dg 関手の実 coslice fiber の左 Hom 表示は、同じ Hom 鎖写像の作用。 -/
lemma dgFunctorCosliceLeftMap_eq_chainMap :
    dgFunctorCosliceLeftMap R F x y = dgLeftPinchedChainMap R D E (F.map x y) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro t
  apply pinchedLeftSimplexVal_injective n
  exact (dgFunctorCosliceLeftMap_simplex R F x y t).trans
    (dgLeftPinchedChainMap_functor_val R F x y t).symm
/-- 同じ実合成比較の fiber 射を、標準左 Hom の同型で移した写像。 -/
def dgFunctorClosedCosliceLeftMap :
    pinchedHomLeft (X := dgNerve R D) (Simplex.vertex x) (Simplex.vertex y) ⟶
      pinchedHomLeft (X := dgNerve R E) (Simplex.vertex q) (Simplex.vertex (F.obj y)) :=
  (pinchedLeftCosliceFiberIso (X := dgNerve R D) (Simplex.vertex x) (Simplex.vertex y)).hom ≫
    dgFunctorClosedCosliceFiber R F x q y s ≫
      (pinchedLeftCosliceFiberIso (X := dgNerve R E)
        (Simplex.vertex q) (Simplex.vertex (F.obj y))).inv
/-- 同じ実合成比較の左 Hom 表示は、元の二つの実左 Hom 写像の合成。 -/
lemma dgFunctorClosedCosliceLeftMap_factorization :
    dgFunctorClosedCosliceLeftMap R F x q y s =
      dgFunctorCosliceLeftMap R F x y ≫ dgCoslicePrecomposeLeftMap R E (F.obj x) q (F.obj y) s := by
  rw [dgFunctorClosedCosliceLeftMap, dgFunctorClosedCosliceFiber_factorization]
  simp only [dgFunctorCosliceLeftMap, dgCoslicePrecomposeLeftMap, Category.assoc,
    Iso.inv_hom_id_assoc]
/-- 同じ実合成比較の左 Hom 表示は、同じ合成 Hom 鎖写像の作用に等しい。 -/
lemma dgFunctorClosedCosliceLeftMap_eq_chainMap :
    dgFunctorClosedCosliceLeftMap R F x q y s =
      dgLeftPinchedChainMap R D E (F.map x y ≫
        eHomWhiskerRight (Complex R) s (ForgetEnrichment.of (Complex R) (F.obj y))) := by
  rw [dgFunctorClosedCosliceLeftMap_factorization, dgFunctorCosliceLeftMap_eq_chainMap,
    dgCoslicePrecomposeLeftMap_eq_chainMap]
  exact (dgLeftPinchedChainMap_comp R _ _).symm
lemma dgFunctorClosedCosliceFiber_isQCatEquivalence
    [QuasiIso (F.map x y ≫ eHomWhiskerRight (Complex R) s
      (ForgetEnrichment.of (Complex R) (F.obj y)))] :
    IsQCatEquivalence (dgFunctorClosedCosliceFiber R F x q y s) := by
  let e := pinchedLeftCosliceFiberIso (X := dgNerve R D)
    (Simplex.vertex x) (Simplex.vertex y)
  let f := pinchedLeftCosliceFiberIso (X := dgNerve R E)
    (Simplex.vertex q) (Simplex.vertex (F.obj y))
  have H : IsQCatEquivalence (dgFunctorClosedCosliceLeftMap R F x q y s) := by
    rw [dgFunctorClosedCosliceLeftMap_eq_chainMap]
    exact dgLeftPinchedChainMap_isQCatEquivalence R D E _
  change IsQCatEquivalence (e.hom ≫ (dgFunctorClosedCosliceFiber R F x q y s ≫ f.inv)) at H
  exact (qCatEquivalenceOfIso f.symm).isQCatEquivalence.cancel_right
    ((qCatEquivalenceOfIso e).isQCatEquivalence.cancel_left H)
lemma dgFunctorClosedCosliceRawFiber_isQCatEquivalence
    [QuasiIso (F.map x y ≫ eHomWhiskerRight (Complex R) s
      (ForgetEnrichment.of (Complex R) (F.obj y)))] :
    IsQCatEquivalence (transportSquareFiberMap
      (sliceUnderProjection ((SSet.yonedaEquiv (X := dgNerve R D)).symm (Simplex.vertex x)))
      (sliceUnderProjection ((SSet.yonedaEquiv (X := dgNerve R E)).symm (Simplex.vertex q)))
      (dgFunctorClosedCosliceMap R F x q s) (dgNerve.map F)
      (dgFunctorClosedCosliceMap_projection R F x q s) (Simplex.vertex y)) := by
  let e := eqToIso (congrArg (vertexFiber (sliceUnderProjection
    ((SSet.yonedaEquiv (X := dgNerve R E)).symm (Simplex.vertex q))))
      (dgFunctorNerve_vertex F y))
  exact (qCatEquivalenceOfIso e).isQCatEquivalence.cancel_right
    (dgFunctorClosedCosliceFiber_isQCatEquivalence R F x q y s)
end SerrePositivity.InfinityCategories
