module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientClosedRoofHomInclusion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedClosedVertexNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientPinchedVertexEdges
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGClosedRoofRefinements

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 任意の指定閉商分子の実屋根頂点は、元の実屋根の像と同じ連結成分にある。 -/
theorem dgStrictQuotientRoofVertex_exists_image_piZero (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    (x y : D) (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x)
    (f : (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.obj s.obj.left ⟶
      ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y)) :
    ∃ z : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P x y) _⦋0⦌,
      SSet.π₀.mk ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y).app (Opposite.op ⦋0⦌) z) =
        SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictQuotientRoofVertex A D P x y s f) := by
  let q₀ := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s.obj.left
  let g := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A (QuotientObject D P) f
  obtain ⟨q, r, hr, t, ht⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFinite_exists_pinchedVertexEdges A D P hP
    q₀ (fun _ : Fin 1 => y) (fun _ => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex g)
  let s' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofRefine A D P x s r hr
  let R := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofRefineHom A D P x s r hr
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.vertexClosedEquiv q y (t 0).toPinched
  obtain ⟨e⟩ := ht 0
  have hs : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A (QuotientObject D P)
      (y := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map r))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex g)).toPinched =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A (QuotientObject D P) ((inclusion A D P).onClosed.map r ≫ f) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedClosedVertexNaturality.pinchedClosedVertex_precompose A (QuotientObject D P) _ f
  have he : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap ((inclusion A D P).map q y) (t 0)).toPinched =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A (QuotientObject D P) ((inclusion A D P).onClosed.map a) := by
    rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedClosedVertexNaturality.pinchedHomChainMap_toPinched, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedClosedVertexNaturality.pinchedClosedVertex_eta A D (t 0).toPinched]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedClosedVertexNaturality.pinchedClosedVertex_map A D (inclusion A D P) a
  let j := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientClosedRoofHomInclusion A D P x y s'
  have hsrc := (congrArg (j.app (Opposite.op ⦋0⦌)) hs).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientClosedRoofHomInclusion_closedVertex A D P x y s' _)
  have htgt := (congrArg (j.app (Opposite.op ⦋0⦌)) he).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientClosedRoofHomInclusion_closedVertex A D P x y s' _)
  have h : SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictQuotientRoofVertex A D P x y s'
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map r ≫ f)) =
      SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictQuotientRoofVertex A D P x y s'
        ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map a)) :=
    (congrArg SSet.π₀.mk hsrc).symm.trans
      ((SSet.π₀.sound (e.map j)).trans (congrArg SSet.π₀.mk htgt))
  refine ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictRoofVertex A D P x y s' a, ?_⟩
  exact (congrArg SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap_strictVertex A D P x y s' a)).trans
    (h.symm.trans (SSet.π₀.sound (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictQuotientRoofRefinementEdge A D P x y R f)))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
