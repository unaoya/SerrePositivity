module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Stable.Quasicategory.CoconeFamilyTranspose
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredInitialPrefixPath

/-!
概要：同じ実分母の終端成分から、全パラメータの前段・次辺比較の共有経路を回収する。
方針：実分数四角形の始点経路と前段辺の終端評価を、同じ一次単体で照合する。
規約：回収円柱の特定の record に依存せず、与えられた実前段辺と次辺族を保持する。
使われ方：完成境界から回収済みの全余錐と元の商余錐を全 attachment で比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.LocalizingInvariants

/-- 同じ実次辺族の商比較四角形を転置した全 Homotopy。 -/
def verdierUniformSpanFractionHomotopy
    {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q) (x z : B.obj _⦋0⦌)
    (d : (verdierDenominatorOver i x : SSet.{u}) _⦋0⦌) {P : SSet.{u}}
    (g : P ⟶ vertexFiber (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i x z) d) :=
  _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanSquareFamilyHomotopy (g ≫ vertexFiberι (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i x z) d ≫
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanEvaluationSquare h x z)

/-- 元の終端一次単体を保つ前段辺と実分数比較の始点経路は、全パラメータで厳密一致。 -/
lemma verdierUniformSpanPrefixPath
    {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q) (x z : B.obj _⦋0⦌)
    (d : (verdierDenominatorOver i x : SSet.{u}) _⦋0⦌) {K : SSet.{u}}
    (g : K ⟶ vertexFiber (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i x z) d)
    {n : ℕ} {D' D : (Δ[n] : SSet.{u}) ⟶ B.obj}
    (t : Truncated.Edge (X := (truncation 2).obj ((ihom Δ[n]).obj B.obj))
      (functorVertex D') (functorVertex D))
    (hlast : (evaluateFunctorAt (Y := B.obj)
      (stdSimplex.obj₀Equiv.symm (Fin.last n))).app (Opposite.op ⦋1⦌) t.edge =
        (roofPointSliceVertexEdge (SSet.yonedaEquiv.symm x) d.val).edge) :
    SSet.yonedaEquiv.symm (functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierUniformSpanFractionHomotopy h x z d g)).edge ≫
        (pre (stdSimplex.δ (1 : Fin 2))).app ((ihom K).obj C.obj) =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanConstantPrefixEdge K q.hom t).edge ≫
        (pre (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n)).app ((ihom K).obj C.obj) := by
  let A₀ := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanConstantPrefixEdge K q.hom t
  have haL : (functorEdgeAt A₀ (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n))).edge =
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanMappedDenominatorEdge i q x d K).edge := by
    have he := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanConstantPrefixEdge_component K q.hom t
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n))
    have hk : SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n) =
        stdSimplex.obj₀Equiv.symm (Fin.last n) := Equiv.apply_symm_apply _ _
    rw [hk, hlast] at he
    have hd : SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanDenominatorDiagram i q x d) =
        (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanMappedDenominator i q x d).edge :=
      (congrArg SSet.yonedaEquiv
        (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanMappedDenominator_diagram i q x d)).symm.trans
          (Equiv.apply_symm_apply _ _)
    have hden := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanMappedDenominatorEdge_edge i q x d K
    rw [SSet.yonedaEquiv_comp, hd] at hden
    exact he.trans hden.symm
  change SSet.yonedaEquiv.symm
    (SSet.yonedaEquiv (curry (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierUniformSpanFractionHomotopy h x z d g).h)) ≫ _ = _
  rw [Equiv.symm_apply_apply, curry_pre_app]
  have hs := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyHomotopy_source h x z d g
  change (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierUniformSpanFractionHomotopy h x z d g).h = _ at hs
  rw [hs]
  apply (cancel_mono (pointFunctorEvaluationIso ((ihom K).obj C.obj)).hom).mp
  change curry (snd (Δ[0] : SSet.{u}) Δ[1] ≫ _ ≫ _) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) =
    (_ ≫ (pre (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n)).app _) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 1))
  rw [curry_evaluateFunctorAt_vertex, Category.assoc, stable_pre_evaluateFunctorAt]
  simp only [← Category.assoc, lift_snd, Category.id_comp]
  have hp : (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) = SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n) := by
    have h₀ : stdSimplex.obj₀Equiv.symm (0 : Fin 1) =
        SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by decide
    rw [h₀, ← SSet.yonedaEquiv_comp, Category.id_comp]
  rw [hp]
  have he : (evaluateFunctorAt (Y := (ihom K).obj C.obj)
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n))).app
      (Opposite.op ⦋1⦌) A₀.edge =
      SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanDenominatorDiagram i q x d ≫
        curry (snd K C.obj)) := by
    exact haL.trans (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanMappedDenominatorEdge_edge i q x d K)
  rw [SSet.yonedaEquiv_symm_comp]
  change _ = SSet.yonedaEquiv.symm
    ((evaluateFunctorAt (Y := (ihom K).obj C.obj)
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n))).app (Opposite.op ⦋1⦌) A₀.edge)
  rw [he, Equiv.symm_apply_apply]

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierUniformSpanFractionHomotopy (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierUniformSpanFractionHomotopy := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierUniformSpanFractionHomotopy

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierUniformSpanPrefixPath := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierUniformSpanPrefixPath
