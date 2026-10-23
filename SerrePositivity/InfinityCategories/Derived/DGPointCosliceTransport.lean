module
public import SerrePositivity.InfinityCategories.Derived.DGFiberTransportSquare
public import SerrePositivity.InfinityCategories.Stable.CoslicePostcompTransport
public import SerrePositivity.InfinityCategories.F1.Joins.CosliceIntervalNaturality
/-!
概要：同じ充満忠実関手に沿う coslice の後合成は、実辺輸送の同値性を保存・反映する。
方針：同じ全 fiber 射を元の pinched Hom の作用へ同定し、実輸送の正方形比較を使う。
規約：単なるホモトピー圏上の充満忠実性で代用しない。
使われ方：coherent nerve から dg nerve への実輸送の移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable {E F : SSet.{u}} (f : E ⟶ F) (x : E _⦋0⦌)
/-- 同じ関手の像の標準点へ正規化した、実 coslice の後合成。 -/
def dgPointCoslicePostcomp : sliceUnder (SSet.yonedaEquiv.symm x) ⟶
    sliceUnder (SSet.yonedaEquiv.symm (f.app (Opposite.op ⦋0⦌) x)) :=
  stableCoslicePostcomp (SSet.yonedaEquiv.symm x) f _ (SSet.yonedaEquiv_symm_comp x f)
/-- 同じ標準点での後合成は、元の関手を底に持つ。 -/
lemma dgPointCoslicePostcomp_projection :
    dgPointCoslicePostcomp f x ≫
      sliceUnderProjection (SSet.yonedaEquiv.symm (f.app (Opposite.op ⦋0⦌) x)) =
        sliceUnderProjection (SSet.yonedaEquiv.symm x) ≫ f :=
  stableCoslicePostcomp_projection _ _ _ _
/-- 同じ実正方形の fiber 射は、元の全 coslice fiber の後合成に一致する。 -/
lemma dgPointCoslicePostcomp_fiber (y : E _⦋0⦌) :
    transportSquareFiberMap (sliceUnderProjection (SSet.yonedaEquiv.symm x))
      (sliceUnderProjection (SSet.yonedaEquiv.symm (f.app (Opposite.op ⦋0⦌) x)))
      (dgPointCoslicePostcomp f x) f (dgPointCoslicePostcomp_projection f x) y =
        pointCosliceFiberMap f x y := by
  apply cosliceFiberUncurry_injective
  change sliceUnderUncurry (_ ≫ vertexFiberι _ _) = _
  rw [transportSquareFiberMap_ι]
  rw [dgPointCoslicePostcomp, stableCoslicePostcomp_uncurry]
  have h := pointCosliceFiberMap_uncurry
    (𝟙 (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y)) f
  simpa only [Category.id_comp, cosliceFiberUncurry] using h.symm
/-- 充満忠実な同じ関手は、coslice の実辺輸送の同値性を保存・反映する。 -/
lemma dgPointCosliceTransport_equivalence_iff [Quasicategory E] [Quasicategory F]
    (hf : IsFullyFaithful f) {y z : E _⦋0⦌} (e : SSet.Edge y z) :
    IsQCatEquivalence (edgeTransport (sliceUnderProjection (SSet.yonedaEquiv.symm x)) e) ↔
      IsQCatEquivalence (edgeTransport
        (sliceUnderProjection (SSet.yonedaEquiv.symm (f.app (Opposite.op ⦋0⦌) x))) (e.map f)) := by
  have hF (b : E _⦋0⦌) : IsQCatEquivalence (transportSquareFiberMap
      (sliceUnderProjection (SSet.yonedaEquiv.symm x))
      (sliceUnderProjection (SSet.yonedaEquiv.symm (f.app (Opposite.op ⦋0⦌) x)))
      (dgPointCoslicePostcomp f x) f (dgPointCoslicePostcomp_projection f x) b) := by
    rw [dgPointCoslicePostcomp_fiber]
    exact (pointCosliceFiberMap_equivalence_iff_pinchedHomMap f x b).mpr (hf x b)
  exact dgLeftFibrationSquareTransport_isQCatEquivalence_iff _ _ _ _ _ e (hF y) (hF z)
end SerrePositivity.InfinityCategories
