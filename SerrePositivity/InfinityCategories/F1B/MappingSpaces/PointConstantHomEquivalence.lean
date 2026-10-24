module
public import SerrePositivity.InfinityCategories.F1.Transport.PointFunctorEvaluation
public import SerrePositivity.InfinityCategories.F1B.Adjunction.ConstantFunctor
public import SerrePositivity.InfinityCategories.Core.EquivalenceFullyFaithful
public import SerrePositivity.InfinityCategories.Core.PrecompositionTensor
/-!
概要：一点をパラメータとする定値関手間の二胞体を、元のホモトピー圏の射と同定する。
方針：一点上の全パラメータ Hom 対応を評価し、同じ左随伴の右随伴の一意性を使う。
規約：全ての射への自然性と、単位・余単位との整合を保持する。
使われ方：一般 kernel の実 RHom と既存の主導来 RHom の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial

/-- 一点上の定値二胞体と、元のホモトピー圏の Hom の全単射。 -/
def pointConstantHomEquiv (X : SSet.{u}) [Quasicategory X] (x y : X _⦋0⦌) :
    ((HomotopyCategory.mk x : hoFunctor.obj X) ⟶ HomotopyCategory.mk y) ≃
      ConstantFunctorHom (Δ[0] : SSet.{u}) X x y := by
  let e := (qCatEquivalenceOfIso
    (pointFunctorEvaluationIso X).symm).isFullyFaithful.toHoFullyFaithful
  exact e.homEquiv.trans (Iso.homCongr
    (eqToIso (congrArg HomotopyCategory.mk (constantFunctorMap_vertex (Δ[0] : SSet.{u}) x)))
    (eqToIso (congrArg HomotopyCategory.mk (constantFunctorMap_vertex (Δ[0] : SSet.{u}) y))))

/-- 一点の Hom 全単射は、元の同じ定値関手の射への作用。 -/
lemma pointConstantHomEquiv_apply (X : SSet.{u}) [Quasicategory X] {x y : X _⦋0⦌}
    (α : (HomotopyCategory.mk x : hoFunctor.obj X) ⟶ HomotopyCategory.mk y) :
    pointConstantHomEquiv X x y α = constantFunctorHomMap (Δ[0] : SSet.{u}) α := rfl
end SerrePositivity.InfinityCategories
