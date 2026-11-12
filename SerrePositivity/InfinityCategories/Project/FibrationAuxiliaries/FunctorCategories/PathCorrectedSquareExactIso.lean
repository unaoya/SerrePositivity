module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.PathCorrectedSquareEdgeCoherence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathFamilyIso

/-!
概要：補正成分の同型を、持ち上げた元の path の辺の類で指定する。
方針：同じ path の関手空間の辺を端点正規化し、同じ一単体の像で coherence を検査する。
規約：存在だけの同型を新しく選ばず、持ち上げた path の類を保持する。
使われ方：元の分類作用との共有頂点でのホモトピー圏の整合性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

variable {A E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
  {q : E ⟶ B} {f : A ⟶ E} {g : A ⟶ B} {e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g (f ≫ q)}

/-- 補正成分と元の成分を結ぶ、持ち上げた同じ path の辺。 -/
def PathCorrectedFunctorSquare.componentEdge (s : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.PathCorrectedFunctorSquare q f g e) :
    Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s.map) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathFamilyEdge s.path).ofEq
    (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s.zero) (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s.one)

/-- 持ち上げた同じ path の辺は可逆。 -/
lemma PathCorrectedFunctorSquare.componentEdge_isInvertible
    (s : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.PathCorrectedFunctorSquare q f g e) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge s.componentEdge.toTruncated := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := s.componentEdge.toTruncated)
    (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathFamilyEdge s.path).toTruncated) rfl).mpr
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathFamilyEdge_isInvertible s.path)

/-- 補正成分の同型の順方向を、持ち上げた同じ path の辺の類に指定する。 -/
def PathCorrectedFunctorSquare.exactComponentIso (s : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.PathCorrectedFunctorSquare q f g e) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso s.map f := by
  letI := s.componentEdge_isInvertible
  exact asIso (SSet.Truncated.HomotopyCategory.homMk s.componentEdge.toTruncated)

/-- 同じ指定 path の成分の辺は、元の自然性の辺そのものへ写る。 -/
lemma PathCorrectedFunctorSquare.componentEdge_over
    (s : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.PathCorrectedFunctorSquare q f g e) :
    ((ihom A).map q).app (Opposite.op ⦋1⦌) s.componentEdge.edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge e).edge := s.path_edge_over

/-- 持ち上げた同じ path の成分同型を標的へ写すと、元の自然性の同型を回収する。 -/
lemma PathCorrectedFunctorSquare.exactComponentIso_postcomp
    (s : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.PathCorrectedFunctorSquare q f g e) :
    s.exactComponentIso.postcomp q =
      eqToIso (congrArg (fun v : A ⟶ B ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex v)) s.comm) ≪≫
        e := by
  have hp := s.componentEdge_over
  rcases s with ⟨m, L, hc, h0, h1, hP⟩
  subst g
  apply Iso.ext
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp, Iso.trans_hom, eqToIso.hom, eqToHom_refl,
    Category.id_comp, Category.comp_id, CategoryTheory.Functor.mapIso_hom]
  change SSet.Truncated.HomotopyCategory.homMk
      ((PathCorrectedFunctorSquare.componentEdge
        (⟨m, L, rfl, h0, h1, hP⟩ : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.PathCorrectedFunctorSquare q f (m ≫ q) e)).toTruncated.map
          ((truncation 2).map ((ihom A).map q))) = e.hom
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge_homMk e]
  apply congrArg SSet.Truncated.HomotopyCategory.homMk
  apply SSet.Truncated.Edge.ext
  exact hp

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
