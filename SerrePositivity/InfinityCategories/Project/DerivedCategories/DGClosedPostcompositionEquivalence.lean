module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedPostcompositionChainMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedPrecompositionEquivalence
public import SerrePositivity.DifferentialGraded.Derived.Projective

/-! # 可逆な実閉辺による全 Hom と pinched Hom の後合成同値

概要：可逆な実閉辺による元の Hom の後合成は準同型で、pinched Hom の実ホモトピー同値。
方針：代表加群からの Hom が準同型を保つことを全 Hom Yoneda 同型で移す。
規約：前三角性は不要。使われ方：商側で閉分母の後合成を有限図式ごと戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- H⁰ で可逆な閉射による全 Hom 鎖後合成は準同型。 -/
lemma dgClosedPostcomposition_quasiIso_of_homotopyIso {x y z : D}
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) z)
    [IsIso ((toHomotopy A D).map s)] : QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition A D (x := x) s) := by
  let f := (_root_.SerrePositivity.DifferentialGraded.dgYoneda A D).onClosed.map s
  have hi : IsIso ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy A D).map f) := by
    change IsIso ((_root_.SerrePositivity.DifferentialGraded.dgYoneda A D).onHomotopy.map ((_root_.SerrePositivity.DifferentialGraded.toHomotopy A D).map s))
    infer_instance
  have hf : moduleQuasiIso A D f := by
    apply (_root_.SerrePositivity.DifferentialGraded.moduleHomotopyQuasiIso_map_iff A D f).mp
    intro w i
    change IsIso ((_root_.SerrePositivity.DifferentialGraded.moduleHomotopyHomology A D w i).map ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy A D).map f))
    infer_instance
  have := _root_.SerrePositivity.DifferentialGraded.moduleHomotopicallyProjective_postcompose_quasiIso A D
    (_root_.SerrePositivity.DifferentialGraded.representable_homotopicallyProjective A D x) f hf
  have : IsIso (_root_.SerrePositivity.DifferentialGraded.yonedaHom A D x y) := by
    dsimp only [_root_.SerrePositivity.DifferentialGraded.yonedaHom]
    infer_instance
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition_yonedaConjugate]
  infer_instance

/-- 可逆な実閉辺による全 Hom 鎖後合成は準同型。 -/
lemma dgClosedPostcomposition_quasiIso_of_invertible {x y z : D}
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) z)
    (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s)) :
    QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition A D (x := x) s) := by
  have hi : IsIso ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence A D).functor.map
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s))) := by
    have : IsIso (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s)) := hs
    infer_instance
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence_map_homMk, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_closed] at hi
  exact dgClosedPostcomposition_quasiIso_of_homotopyIso A D s

/-- 指定閉射による、元の実 pinched Hom の後合成。 -/
def pinchedClosedPostcomposition {x y z : D}
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x z :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition A D s)

/-- 可逆な実閉辺による pinched 後合成は、実ホモトピー同値。 -/
lemma pinchedClosedPostcomposition_equivalence_of_invertible {x y z : D}
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) z)
    (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (pinchedClosedPostcomposition A D (x := x) s) := by
  have := dgClosedPostcomposition_quasiIso_of_invertible A D (x := x) s hs
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_quasiIso_equivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition A D s)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
