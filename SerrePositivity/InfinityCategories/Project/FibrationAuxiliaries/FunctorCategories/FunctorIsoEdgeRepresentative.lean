module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftFibrationEdgeRepresentative
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibrationInternalHom
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransport
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerHom
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy

/-!
概要：関手同型の同じ像を、両端を固定した指定代表辺へ揃える。
方針：関手空間の左ファイブレーションに元の辺の代表変更を適用する。
規約：元の関手同型の類と全パラメーターの両端を保持する。
使われ方：補正成分の円柱を同じ共有頂点で貼り合わせる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 同じ像の指定同型を保って、元の関手同型の辺を両端固定で揃え直せる。 -/
lemma functorIso_exists_edge_representative_over
    {A X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (q : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] {f g : A ⟶ X} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g)
    {f' g' : A ⟶ Y} (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f' g') (hf : f ≫ q = f') (hg : g ≫ q = g')
    (h : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (e.postcomp q) hf hg = d)
    (r : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom A).obj Y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f') (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g'))
    (hr : SSet.Truncated.HomotopyCategory.homMk r = d.hom) :
    ∃ e' : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom A).obj X))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g),
      ((ihom A).map q).app (Opposite.op ⦋1⦌) e'.edge = r.edge ∧
      SSet.Truncated.HomotopyCategory.homMk e' = e.hom := by
  subst f' g'
  have hh : e.postcomp q = d := eq_of_heq
    ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq (e.postcomp q) rfl rfl).symm.trans (heq_of_eq h))
  have hc : SSet.Truncated.HomotopyCategory.homMk r =
      SSet.Truncated.HomotopyCategory.homMk
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge e).map ((truncation 2).map ((ihom A).map q))) := by
    rw [hr, ← hh, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_hom,
      ← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge_homMk]
    rfl
  obtain ⟨e', he', hc'⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibration_exists_edge_representative_over
    ((ihom A).map q) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge e) r hc
  exact ⟨e', congrArg SSet.Truncated.Edge.edge he',
    hc'.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge_homMk e)⟩

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
