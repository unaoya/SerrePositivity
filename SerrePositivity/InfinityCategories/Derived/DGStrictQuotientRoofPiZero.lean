module
public import SerrePositivity.InfinityCategories.Derived.DGQuotientClosedRoofHomInclusion
public import SerrePositivity.InfinityCategories.Derived.PinchedClosedVertexNaturality
public import SerrePositivity.InfinityCategories.Derived.DGQuotientPinchedVertexEdges
public import SerrePositivity.InfinityCategories.Derived.DGClosedRoofRefinements

/-! # 指定商屋根頂点を元の実屋根の像に結ぶ

概要：任意の閉商分子を持つ指定屋根頂点は、元の実屋根の像と同じ連結成分にある。
方針：有限頂点持ち上げの実辺を細分後の実 fiber に含め、指定細分辺と接続する。
規約：弱同値性は未主張。使われ方：実屋根比較の連結成分上の全射性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGQuotient DGNerve DGNerve.PinchedHom SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

/-- 任意の指定閉商分子の実屋根頂点は、元の実屋根の像と同じ連結成分にある。 -/
theorem dgStrictQuotientRoofVertex_exists_image_piZero (P : Set D) (hP : localKFlat A D P)
    (x y : D) (s : DGClosedVerdierDenominators A D P x)
    (f : (inclusion A D P).onClosed.obj s.obj.left ⟶
      ForgetEnrichment.of (Complex A) ((inclusion A D P).obj y)) :
    ∃ z : (dgRoofCorrespondence A D P x y) _⦋0⦌,
      SSet.π₀.mk ((dgRoofCorrespondenceMap A D P x y).app (Opposite.op ⦋0⦌) z) =
        SSet.π₀.mk (dgStrictQuotientRoofVertex A D P x y s f) := by
  let q₀ := ForgetEnrichment.to (Complex A) s.obj.left
  let g := pinchedClosedVertex A (QuotientObject D P) f
  obtain ⟨q, r, hr, t, ht⟩ := dgQuotientFinite_exists_pinchedVertexEdges A D P hP
    q₀ (fun _ : Fin 1 => y) (fun _ => toLinearSimplex g)
  let s' := dgClosedRoofRefine A D P x s r hr
  let R := dgClosedRoofRefineHom A D P x s r hr
  let a := vertexClosedEquiv q y (t 0).toPinched
  obtain ⟨e⟩ := ht 0
  have hs : (pinchedLinearSimplexMap (dgClosedPrecomposition A (QuotientObject D P)
      (y := (inclusion A D P).obj y) ((inclusion A D P).onClosed.map r))
      (toLinearSimplex g)).toPinched =
      pinchedClosedVertex A (QuotientObject D P) ((inclusion A D P).onClosed.map r ≫ f) :=
    pinchedClosedVertex_precompose A (QuotientObject D P) _ f
  have he : (pinchedLinearSimplexMap ((inclusion A D P).map q y) (t 0)).toPinched =
      pinchedClosedVertex A (QuotientObject D P) ((inclusion A D P).onClosed.map a) := by
    rw [← pinchedHomChainMap_toPinched, ← pinchedClosedVertex_eta A D (t 0).toPinched]
    exact pinchedClosedVertex_map A D (inclusion A D P) a
  let j := dgQuotientClosedRoofHomInclusion A D P x y s'
  have hsrc := (congrArg (j.app (Opposite.op ⦋0⦌)) hs).trans
    (dgQuotientClosedRoofHomInclusion_closedVertex A D P x y s' _)
  have htgt := (congrArg (j.app (Opposite.op ⦋0⦌)) he).trans
    (dgQuotientClosedRoofHomInclusion_closedVertex A D P x y s' _)
  have h : SSet.π₀.mk (dgStrictQuotientRoofVertex A D P x y s'
      ((inclusion A D P).onClosed.map r ≫ f)) =
      SSet.π₀.mk (dgStrictQuotientRoofVertex A D P x y s'
        ((inclusion A D P).onClosed.map a)) :=
    (congrArg SSet.π₀.mk hsrc).symm.trans
      ((SSet.π₀.sound (e.map j)).trans (congrArg SSet.π₀.mk htgt))
  refine ⟨dgStrictRoofVertex A D P x y s' a, ?_⟩
  exact (congrArg SSet.π₀.mk (dgRoofCorrespondenceMap_strictVertex A D P x y s' a)).trans
    (h.symm.trans (SSet.π₀.sound (dgStrictQuotientRoofRefinementEdge A D P x y R f)))

end SerrePositivity.InfinityCategories
