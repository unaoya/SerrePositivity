module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceRetractionMappingFiber
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.PushoutSpanSourceFiber
public import SerrePositivity.InfinityCategories.Stable.PastingSplitProjection
public import SerrePositivity.InfinityCategories.Core.FiniteShapes

/-!
概要：終対象の終域への pushout の指定 fiber を、上辺の retraction 空間から可縮にする。
方針：元の上辺を同じ終域から出る閉包内辺として保持し、構成済みの基点付き比較を使う。
規約：終対象の存在は仮定。元の左辺の終点制限が恒等余錐であることを明示する。
使われ方：HTT 5.5.5.13–14 の pushout と全写像空間の局所性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 元の上辺の恒等基点上の fiber は、終対象の retraction 空間により可縮となる。 -/
lemma generatedSource_terminal_squareTopFiber_contractible
    (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (s : (generatedSourceCategory edges x) _⦋0⦌) (hs : IsTerminalVertex s)
    (R : (Δ[1] : SSet.{u + 1}) ⊗ Δ[1] ⟶ C) (hR : IsPushoutSquare R)
    (hf : SSet.yonedaEquiv (squareBottomEdge ≫ R) ∈ generatedEdges edges)
    (hy : squareVertex R 0 1 = (generatedSourceTarget edges x).app _ s)
    (d : (coconeMappingSpace (squareLeftEdge ≫ R)
      ((generatedSourceTarget edges x).app _ s)) _⦋0⦌)
    (hd : (((cosliceRestrictionFiberMap (squareLeftEdge ≫ R) (stdSimplex.δ (0 : Fin 2))
      ((generatedSourceTarget edges x).app _ s)).app _ d).val).val =
        SSet.const ((generatedSourceTarget edges x).app _ s)) :
    IsContractibleKan (vertexFiber (squareTopSourceMappingRestriction R
      ((generatedSourceTarget edges x).app _ s))
      ((cosliceRestrictionFiberMap (squareLeftEdge ≫ R) (stdSimplex.δ (0 : Fin 2))
        ((generatedSourceTarget edges x).app _ s)).app _ d)) := by
  let v : C.Edge ((generatedSourceTarget edges x).app _ s) (squareVertex R 1 1) :=
    { edge := (squareTopArrow R).edge
      src_eq := (squareTopArrow R).src_eq.trans hy
      tgt_eq := (squareTopArrow R).tgt_eq }
  have hv : v.edge ∈ generatedEdges edges := by
    change (squareTopArrow R).edge ∈ generatedEdges edges
    rw [squareTopArrow_edge]
    exact (stronglySaturatedClosure_stronglySaturated
      (SSet.uliftFunctor.{u + 1, u}).obj (Set.range edges)).2.1 R hR hf
  have he : SSet.yonedaEquiv.symm v.edge = squareTopEdge ≫ R := by
    change SSet.yonedaEquiv.symm (squareTopArrow R).edge = _
    rw [squareTopArrow_edge]
    exact SSet.yonedaEquiv.symm_apply_apply _
  have ha : stdSimplex.δ (0 : Fin 2) ≫ (squareLeftEdge ≫ R) =
      SSet.yonedaEquiv.symm ((generatedSourceTarget edges x).app _ s) := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, squareLeftEdge_target, hy, Equiv.apply_symm_apply]
  exact generatedSource_terminal_normalizedMappingFiber_contractible edges x s hs v hv
    (squareTopEdge ≫ R) he _ (squareTopSource_eq_leftTarget R) ha _ hd

/-- 元の底辺の始点制限の同じ指定 fiber も、pushout 比較により可縮となる。 -/
lemma generatedSource_terminal_pushout_sourceFiber_contractible
    (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (s : (generatedSourceCategory edges x) _⦋0⦌) (hs : IsTerminalVertex s)
    (R : (Δ[1] : SSet.{u + 1}) ⊗ Δ[1] ⟶ C) (hR : IsPushoutSquare R)
    (hf : SSet.yonedaEquiv (squareBottomEdge ≫ R) ∈ generatedEdges edges)
    (hy : squareVertex R 0 1 = (generatedSourceTarget edges x).app _ s)
    (d : (coconeMappingSpace (squareLeftEdge ≫ R)
      ((generatedSourceTarget edges x).app _ s)) _⦋0⦌)
    (hd : (((cosliceRestrictionFiberMap (squareLeftEdge ≫ R) (stdSimplex.δ (0 : Fin 2))
      ((generatedSourceTarget edges x).app _ s)).app _ d).val).val =
        SSet.const ((generatedSourceTarget edges x).app _ s)) :
    IsContractibleKan (vertexFiber (cosliceRestrictionFiberMap (horn₂₀.ι₀₁ ≫ pushoutSpan R)
      (stdSimplex.δ (1 : Fin 2)) ((generatedSourceTarget edges x).app _ s))
      ((pushoutSpanRightBase R ((generatedSourceTarget edges x).app _ s)).app _ d)) :=
  (pushoutSourceFiber_contractible_iff R hR ((generatedSourceTarget edges x).app _ s) d).mpr
    (generatedSource_terminal_squareTopFiber_contractible edges x s hs R hR hf hy d hd)

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
