module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.GeneratedSource
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.NativeCoconeFamilyEvaluation
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorVertexConeReindex
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PreFiberKan

/-!
概要：固定始域の閉包内 coslice の全単体を、元の飽和射圏へ送る。
方針：全余錐族を一点と一点の join 同型で制限し、元の脚の所属で持ち上げる。
規約：頂点だけの選択から関手を作らず、元の coherent な余錐族を保持する。
使われ方：固定始域圏と飽和射圏の比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 元の全 coslice の余錐族を、そのまま元の射の族へ制限する。 -/
def sourceCosliceArrowFamily (x : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm x) ⟶ (ihom (Δ[1] : SSet.{u + 1})).obj C :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeFunctorFamily (SSet.yonedaEquiv.symm x) ≫
    (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv).app C

omit [Quasicategory C] in
/-- 制限した射族の各頂点は、元の同じ余錐の指定脚である。 -/
lemma sourceCosliceArrowFamily_vertex (x : C _⦋0⦌)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (SSet.yonedaEquiv.symm x)) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowVertexEdge ((sourceCosliceArrowFamily x).app _ c) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.leg c (𝟙 Δ[0])).edge := by
  change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[1] C).symm
    (((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv).app C).app _
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeFunctorFamily (SSet.yonedaEquiv.symm x)).app _ c))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeFunctorFamily_vertex, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexMap_precomp]
  change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ c.val) =
    SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (𝟙 Δ[0]) ≫ c.val)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_id, Category.id_comp]

/-- 元の coherent な脚の族を、飽和射の全部分圏へ送る。 -/
def generatedSourceArrows (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceCategory edges x ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowCategory edges :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceInclusion edges x ≫ sourceCosliceArrowFamily x)
    (fun c ↦ by
      change _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowVertexEdge ((sourceCosliceArrowFamily x).app _ c.val) ∈ _
      rw [sourceCosliceArrowFamily_vertex]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex c)

/-- 射圏への比較は、元の余錐族から作った同じ全単体の射を回収する。 -/
lemma generatedSourceArrows_inclusion (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    generatedSourceArrows edges x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowInclusion edges =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceInclusion edges x ≫ sourceCosliceArrowFamily x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

omit [Quasicategory C] in
/-- 元の脚の族の終点評価は、元の coslice 射影そのもの。 -/
lemma sourceCosliceArrowFamily_target (x : C _⦋0⦌) :
    sourceCosliceArrowFamily x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x) := by
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm 1) = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coconeRightApexVertex Δ[0] := by
    apply SSet.yonedaEquiv.symm.injective
    rw [← SSet.yonedaEquiv_symm_comp]
    have hv : SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u + 1}) ⟶ Δ[1]) := by
      apply SSet.yonedaEquiv.injective
      apply SSet.stdSimplex.ext
      intro i
      fin_cases i
      rfl
    rw [hv]
    change _ = SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] Δ[0]).app _
      (SSet.yonedaEquiv (𝟙 Δ[0])))
    rw [← SSet.yonedaEquiv_symm_comp, Equiv.symm_apply_apply, Category.id_comp]
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inr, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [sourceCosliceArrowFamily, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.evaluateFunctorAt_pre, he,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeFunctorFamily_apex]

/-- 飽和射圏への比較の終点は、元の固定始域圏の終域射影に厳密に一致する。 -/
lemma generatedSourceArrows_target (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    generatedSourceArrows edges x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowInclusion edges ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1) = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceTarget edges x := by
  rw [← Category.assoc, generatedSourceArrows_inclusion, Category.assoc,
    sourceCosliceArrowFamily_target]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
