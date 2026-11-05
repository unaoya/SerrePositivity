module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.F1.Transport.CosliceTransportPointHom

/-! # 元の矢印の類の等式を、同じ実 coslice fiber 内の道へ戻す -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.F1.Transport
open SerrePositivity.KST.Fibration
variable {X : SSet.{u}} {x a : X _⦋0⦌}
  {v w : (vertexFiber (sliceUnderProjection (yonedaEquiv.symm x)) a) _⦋0⦌}

/-- 元の矢印の左ホモトピー三角形は、同じ終点を固定した実 coslice fiber の辺になる。 -/
def cosliceFiberEdgeOfHomotopy (t : SSet.Edge.CompStruct (cosliceFiberVertexToEdge v)
    (SSet.Edge.id a) (cosliceFiberVertexToEdge w)) : SSet.Edge v w := by
  let H := (joinStdSimplexIso 0 1).hom ≫ SSet.yonedaEquiv.symm t.simplex
  have hinl : joinInl (Δ[0] : SSet.{u}) Δ[1] ≫ (joinStdSimplexIso 0 1).hom =
      stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) := by
    apply SSet.yonedaEquiv.injective
    decide
  have hf : joinInl Δ[0] Δ[1] ≫ H = SSet.yonedaEquiv.symm x := by
    dsimp only [H]
    rw [← Category.assoc, hinl, Category.assoc,
      stdSimplex.δ_comp_yonedaEquiv_symm]
    change stdSimplex.δ (1 : Fin 2) ≫
      SSet.yonedaEquiv.symm (X.δ 2 t.simplex) = _
    rw [t.d₂]
    exact (cosliceFiberVertexToEdge v).δ_one_yonedaEquiv_symm
  let s : (sliceUnder (SSet.yonedaEquiv.symm x)) _⦋1⦌ := ⟨H, hf⟩
  have hb : (sliceUnderProjection (SSet.yonedaEquiv.symm x)).app (Opposite.op ⦋1⦌) s =
      PinchedHom.constant a 1 := by
    change SSet.yonedaEquiv (joinInr Δ[0] Δ[1] ≫ H) = _
    dsimp only [H]
    rw [← Category.assoc, joinStdSimplexIso_one_inr,
      stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.apply_symm_apply]
    exact t.d₀.trans (pinchedConstant_one a).symm
  refine ⟨⟨s, hb⟩, ?_, ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    change joinMap (𝟙 Δ[0]) (stdSimplex.δ (1 : Fin 2)) ≫ H = v.val.val
    dsimp only [H]
    rw [← Category.assoc, joinStdSimplexIso_vertex_one, Category.assoc,
      stdSimplex.δ_comp_yonedaEquiv_symm]
    change (joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm (X.δ 2 t.simplex) = _
    rw [t.d₂]
    exact congrArg (fun z : (vertexFiber
      (sliceUnderProjection (SSet.yonedaEquiv.symm x)) a) _⦋0⦌ => z.val.val)
      ((cosliceFiberVertexEquiv x a).symm_apply_apply v)
  · apply Subtype.ext
    apply Subtype.ext
    change joinMap (𝟙 Δ[0]) (stdSimplex.δ (0 : Fin 2)) ≫ H = w.val.val
    dsimp only [H]
    rw [← Category.assoc, joinStdSimplexIso_vertex_one, Category.assoc,
      stdSimplex.δ_comp_yonedaEquiv_symm]
    change (joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm (X.δ 1 t.simplex) = _
    rw [t.d₁]
    exact congrArg (fun z : (vertexFiber
      (sliceUnderProjection (SSet.yonedaEquiv.symm x)) a) _⦋0⦌ => z.val.val)
      ((cosliceFiberVertexEquiv x a).symm_apply_apply w)

/-- 元の矢印の類の等式から、同じ実 coslice fiber 内で元の二点を結ぶ同型を回収する。 -/
def cosliceFiberVertexIsoOfHomEq [Quasicategory X]
    (h : cosliceFiberPointHom v = cosliceFiberPointHom w) : VertexIso v w := by
  have h₂ : Truncated.HomotopyCategory₂.homMk (cosliceFiberVertexToEdge v).toTruncated =
      Truncated.HomotopyCategory₂.homMk (cosliceFiberVertexToEdge w).toTruncated := by
    have hh := congrArg (fun m => (pathToEdgeHomotopyCategory ((truncation 2).obj X)).map m) h
    simpa only [pathToEdgeHomotopyCategory, cosliceFiberPointHom,
      Truncated.HomotopyCategory.lift_map_homMk] using hh
  have hL : Truncated.HomotopicL (cosliceFiberVertexToEdge v).toTruncated
      (cosliceFiberVertexToEdge w).toTruncated := Quotient.exact h₂
  let t := Classical.choice hL
  let e := cosliceFiberEdgeOfHomotopy t
  have := vertexFiber_kanComplex_of_leftFibration
    (sliceUnderProjection (SSet.yonedaEquiv.symm x)) a
  have : IsIso (Truncated.HomotopyCategory.homMk e.toTruncated) :=
    IsGroupoid.all_isIso (C := hoFunctor.obj
      (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) a)) _
  exact asIso (Truncated.HomotopyCategory.homMk e.toTruncated)

end SerrePositivity.InfinityCategories.F1.Transport

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberEdgeOfHomotopy (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.cosliceFiberEdgeOfHomotopy := _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberEdgeOfHomotopy

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberVertexIsoOfHomEq (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.cosliceFiberVertexIsoOfHomEq := _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberVertexIsoOfHomEq

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.cosliceFiberEdgeOfHomotopy._proof_1 := _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberEdgeOfHomotopy._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.cosliceFiberEdgeOfHomotopy._proof_2 := _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberEdgeOfHomotopy._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.cosliceFiberEdgeOfHomotopy._proof_3 := _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberEdgeOfHomotopy._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.cosliceFiberEdgeOfHomotopy._proof_4 := _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberEdgeOfHomotopy._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.cosliceFiberEdgeOfHomotopy._proof_5 := _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberEdgeOfHomotopy._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.cosliceFiberEdgeOfHomotopy._proof_6 := _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberEdgeOfHomotopy._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.cosliceFiberEdgeOfHomotopy._proof_7 := _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberEdgeOfHomotopy._proof_7

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.cosliceFiberEdgeOfHomotopy._proof_8 := _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberEdgeOfHomotopy._proof_8

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.cosliceFiberVertexIsoOfHomEq._proof_1 := _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberVertexIsoOfHomEq._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.cosliceFiberVertexIsoOfHomEq._proof_2 := _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberVertexIsoOfHomEq._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.cosliceFiberVertexIsoOfHomEq._proof_3 := _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberVertexIsoOfHomEq._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.cosliceFiberVertexIsoOfHomEq._proof_4 := _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberVertexIsoOfHomEq._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.cosliceFiberVertexIsoOfHomEq._proof_5 := _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberVertexIsoOfHomEq._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.cosliceFiberVertexIsoOfHomEq._proof_6 := _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberVertexIsoOfHomEq._proof_6
