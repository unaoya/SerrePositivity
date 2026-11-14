module

public import SerrePositivity.KST.NonConnective.DGKappaFullPerfAction
public import SerrePositivity.KST.NonConnective.DGKappaSplitRelations
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.NerveInclusion
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare

/-!
概要：同じ実注入・射影・零自己関手から作る、全 native Perf 作用の実四角形。
方針：全関手 Hom 内の交差合成の等式で二つの実二単体を貼り、全作用へ写す。
規約：点ごとの cofiber 性の証明は別工程であり、ここでは仮定しない。
使われ方：同じ Perf 上の実分裂 cofiber 族。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 同じ全次数 Hom end を持つ dg 関手圏の閉零圏。 -/
abbrev DGKappaClosedFunctorCategory :=
  ClosedCategory R (DGFunctor R (DGKappaCone R D I) (DGKappaCone R D I))

/-- 閉射の通常 nerve を、同じ全 native 入力へ持ち上げる実写像。 -/
def dgKappaClosedFunctorNativeMap :
    nerve (DGKappaClosedFunctorCategory R D I) ⟶ dgKappaFullPerfParameter R D I where
  app n := ↾fun x ↦ ULift.up ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion R
    (DGFunctor R (DGKappaCone R D I) (DGKappaCone R D I))).app n x)
  naturality _ _ f := by
    ext x
    apply ULift.ext
    exact NatTrans.naturality_apply (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion R
      (DGFunctor R (DGKappaCone R D I) (DGKappaCone R D I))) f x

/-- 同じ左注入と右射影を持つ、元の閉関手圏の下二単体。 -/
def dgKappaSplitClosedLower : (nerve (DGKappaClosedFunctorCategory R D I)) _⦋2⦌ :=
  ComposableArrows.mk₂ (dgKappaSplitHead R D I) (dgKappaSplitTailProjection R D I)

/-- 同じ実零自己関手を経由する、元の閉関手圏の上二単体。 -/
def dgKappaSplitClosedUpper (Z : DGKappaZeroInput R D I) :
    (nerve (DGKappaClosedFunctorCategory R D I)) _⦋2⦌ :=
  ComposableArrows.mk₂
    (0 : ForgetEnrichment.of (Complex R) (DGFunctor.id (A := R) (DGKappaCone R D I)) ⟶
      ForgetEnrichment.of (Complex R) (dgKappaZeroFunctor R D I Z))
    (0 : ForgetEnrichment.of (Complex R) (dgKappaZeroFunctor R D I Z) ⟶
      ForgetEnrichment.of (Complex R) (dgKappaConeCountableSum R D I))

/-- 二つの指定二単体の共有対角は、同じ全 Hom の零射として厳密に一致する。 -/
lemma dgKappaSplitClosed_shared (Z : DGKappaZeroInput R D I) :
    (nerve (DGKappaClosedFunctorCategory R D I)).δ 1 (dgKappaSplitClosedUpper R D I Z) =
      (nerve (DGKappaClosedFunctorCategory R D I)).δ 1 (dgKappaSplitClosedLower R D I) := by
  rw [dgKappaSplitClosedUpper, dgKappaSplitClosedLower,
    nerve.δ₁_mk₂_eq, nerve.δ₁_mk₂_eq, zero_comp, dgKappaSplit_head_tail]

/-- 同じ元の閉関手圏の両二単体を貼り合わせた実四角形。 -/
def dgKappaSplitClosedSquare (Z : DGKappaZeroInput R D I) :
    (Δ[1] : SSet.{max (u + 1) v}) ⊗ Δ[1] ⟶ nerve (DGKappaClosedFunctorCategory R D I) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.desc (SSet.yonedaEquiv.symm (dgKappaSplitClosedUpper R D I Z))
    (SSet.yonedaEquiv.symm (dgKappaSplitClosedLower R D I)) (by
      rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm,
        dgKappaSplitClosed_shared])

/-- 同じ四角形を全 native 入力へ写す。 -/
def dgKappaSplitFullNativeSquare (Z : DGKappaZeroInput R D I) :
    (Δ[1] : SSet.{max (u + 1) v}) ⊗ Δ[1] ⟶ dgKappaFullPerfParameter R D I :=
  dgKappaSplitClosedSquare R D I Z ≫ dgKappaClosedFunctorNativeMap R D I

/-- 同じ実分裂四角形を、元の Perf の全関手空間へ送る実族。 -/
def dgKappaSplitPerfFamilySquare (Z : DGKappaZeroInput R D I) :=
  dgKappaSplitFullNativeSquare R D I Z ≫ dgKappaFullPerfFamilyMap R D I

end SerrePositivity.KST.NonConnective
