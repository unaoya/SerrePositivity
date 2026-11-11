module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRelativeKFlatResolutionLocalization
/-!
概要：K-flat 全部分圏の準同型辺から、元の両 K-flat 加群間の実閉準同型を回収する。
方針：辺条件の同じ閉射表示と、両端頂点の実 K-flat 条件を照合する。
規約：辺や両端を選び直さない。使われ方：任意 kernel による準同型保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- K-flat 準同型辺を表す元の閉射の始点も、同じ実加群の K-flat 条件を持つ。 -/
lemma dgRelativeKFlatEdge_source_relativeKFlat
    (s : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleNerve R E) _⦋1⦌)
    {M N : _root_.SerrePositivity.DifferentialGraded.ClosedCategory R (_root_.SerrePositivity.DifferentialGraded.RightModule R E)} (f : M ⟶ N)
    (he : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R (RightModule R E) f).edge = s.val) :
    _root_.SerrePositivity.DifferentialGraded.moduleRelativeKFlat R E (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M) := by
  have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleNerve R E).δ 1 s)
  change _root_.SerrePositivity.DifferentialGraded.moduleRelativeKFlat R E
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R E).δ 1 s.val)) at hx
  have hm := congrArg (fun t => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R E).δ 1 t)) he
  change ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R E).δ 1 s.val) at hm
  exact hm.symm ▸ hx
/-- K-flat 準同型辺を表す元の閉射の終点も、同じ実加群の K-flat 条件を持つ。 -/
lemma dgRelativeKFlatEdge_target_relativeKFlat
    (s : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleNerve R E) _⦋1⦌)
    {M N : _root_.SerrePositivity.DifferentialGraded.ClosedCategory R (_root_.SerrePositivity.DifferentialGraded.RightModule R E)} (f : M ⟶ N)
    (he : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R (RightModule R E) f).edge = s.val) :
    _root_.SerrePositivity.DifferentialGraded.moduleRelativeKFlat R E (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) N) := by
  have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleNerve R E).δ 0 s)
  change _root_.SerrePositivity.DifferentialGraded.moduleRelativeKFlat R E
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R E).δ 0 s.val)) at hx
  have hm := congrArg (fun t => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R E).δ 0 t)) he
  change ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) N =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R E).δ 0 s.val) at hm
  exact hm.symm ▸ hx
/-- K-flat 加群間の実閉準同型辺を反転すれば、同じ全部分圏の全準同型辺を反転する。 -/
lemma dgRelativeKFlatQuasiIsomorphismEdges_inverts {Y : SSet.{max (u + 1) v}}
    (q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R E ⟶ Y)
    (h : ∀ (M N : _root_.SerrePositivity.DifferentialGraded.ClosedCategory R (_root_.SerrePositivity.DifferentialGraded.RightModule R E)),
      _root_.SerrePositivity.DifferentialGraded.moduleRelativeKFlat R E (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M) →
      _root_.SerrePositivity.DifferentialGraded.moduleRelativeKFlat R E (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) N) →
      ∀ f : M ⟶ N, moduleQuasiIso R E f → _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R (RightModule R E) f).map ((truncation 2).map q))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R E ≫ q)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatQuasiIsomorphismEdges R E) := by
  intro s hs
  obtain ⟨M, N, f, hf, he⟩ := hs
  have hi := h M N (dgRelativeKFlatEdge_source_relativeKFlat R E s f he)
    (dgRelativeKFlatEdge_target_relativeKFlat R E s f he) f hf
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (X := Y)
    (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s).map
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R E ≫ q)))
    (f := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R (RightModule R E) f).map ((truncation 2).map q))
    (congrArg (fun t => q.app (Opposite.op ⦋1⦌) t) he.symm)).mpr hi
end SerrePositivity.InfinityCategories.Project.DerivedCategories
