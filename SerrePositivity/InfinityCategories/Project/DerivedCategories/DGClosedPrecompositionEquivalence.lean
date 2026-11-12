module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedClosedPrecomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedEdges
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedChainMapQuasiIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStableHomotopyEdges
public import SerrePositivity.DifferentialGraded.Derived.Projective

/-! # 可逆な実閉辺による全 Hom と pinched Hom の前合成同値

概要：H⁰ で可逆な閉射の全 Hom 前合成は準同型、実 pinched 前合成はホモトピー同値。
方針：Yoneda の全 Hom 同型と、代表加群間の射影的な前合成へ移す。
規約：前三角性・商の平坦性は不要。使われ方：商側の屋根図式の全細分の同値性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- H⁰ で可逆な閉射による全 Hom 鎖前合成は準同型。 -/
lemma dgClosedPrecomposition_quasiIso_of_homotopyIso {q x y : D}
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)
    [IsIso ((toHomotopy A D).map s)] : QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A D (y := y) s) := by
  let f := (_root_.SerrePositivity.DifferentialGraded.dgYoneda A D).onClosed.map s
  have hi : IsIso ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy A D).map f) := by
    change IsIso ((_root_.SerrePositivity.DifferentialGraded.dgYoneda A D).onHomotopy.map ((_root_.SerrePositivity.DifferentialGraded.toHomotopy A D).map s))
    infer_instance
  have hf : moduleQuasiIso A D f := by
    apply (_root_.SerrePositivity.DifferentialGraded.moduleHomotopyQuasiIso_map_iff A D f).mp
    intro z i
    change IsIso ((_root_.SerrePositivity.DifferentialGraded.moduleHomotopyHomology A D z i).map ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy A D).map f))
    infer_instance
  have := _root_.SerrePositivity.DifferentialGraded.moduleHomotopicallyProjective_precompose_quasiIso A D
    (_root_.SerrePositivity.DifferentialGraded.representable_homotopicallyProjective A D q) (_root_.SerrePositivity.DifferentialGraded.representable_homotopicallyProjective A D x)
    f hf (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.representable A y))
  have : IsIso (_root_.SerrePositivity.DifferentialGraded.yonedaHom A D x y) := by
    dsimp only [_root_.SerrePositivity.DifferentialGraded.yonedaHom]
    infer_instance
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition]
  infer_instance

/-- 可逆な実閉辺による全 Hom 鎖前合成は準同型。 -/
lemma dgClosedPrecomposition_quasiIso_of_invertible {q x y : D}
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)
    (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s)) :
    QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A D (y := y) s) := by
  have hi : IsIso ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence A D).functor.map
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s))) := by
    have : IsIso (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s)) := hs
    infer_instance
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence_map_homMk, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_closed] at hi
  exact dgClosedPrecomposition_quasiIso_of_homotopyIso A D s

/-- 可逆な実閉辺による pinched 前合成は実ホモトピー同値。 -/
lemma pinchedClosedPrecomposition_equivalence_of_invertible {q x y : D}
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)
    (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A D (y := y) s) := by
  have := dgClosedPrecomposition_quasiIso_of_invertible A D (y := y) s hs
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_quasiIso_equivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A D s)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
