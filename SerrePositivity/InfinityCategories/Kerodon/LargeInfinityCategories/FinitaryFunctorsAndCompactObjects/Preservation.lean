module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.Definition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SquareFunctorTransport

/-!
概要：κ-filtered 余極限保存の全自然同型不変性と、一つの余極限余錐による判定。
方針：元の全余錐の関手同型で普遍性を移す。
規約：余極限が存在しない図式に、選択した余錐を要求しない。
使われ方：Map(x,−) の具体的模型による κ-compact 性の証明。

対応節は Kerodon 9.2（Tag 0639）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
variable {κ : Cardinal.{u}} {C : SSet.{max u v}} {Y : SSet.{max u v + 1}}
  [Quasicategory Y]
  {F G : (SSet.uliftFunctor.{max u v + 1, max u v}).obj C ⟶ Y}

/-- 元の全自然同型で比較される関手は、同じ κ-filtered 余極限保存性を持つ。 -/
lemma PreservesKappaFilteredColimits.of_functorIso
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits.{u, v} κ F) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits.{u, v} κ G := by
  intro I hI hFiltered D c hc
  exact (h I D c hc).of_functorIso (e.precomp (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift c).val)

/-- 元の各図式の、一つの全余極限余錐の像だけを調べれば保存性を判定できる。 -/
lemma preservesKappaFilteredColimits_of_exists [Quasicategory C]
    (h : ∀ (I : SSet.{u}) [Quasicategory I] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ I]
      (D : (SSet.uliftFunctor.{v, u}).obj I ⟶ C), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit D →
        ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ∧
          _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone F (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift c))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits.{u, v} κ F := by
  intro I hI hFiltered D c hc
  obtain ⟨d, hd, hFd⟩ := h I D ⟨c, hc⟩
  let c' := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift.{max u v, max u v + 1} c
  let d' := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift.{max u v, max u v + 1} d
  have hc' : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c' := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isColimitCone_iff_ulift c).mp hc
  have hd' : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d' := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isColimitCone_iff_ulift d).mp hd
  exact hFd.of_functorIso
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFunctorIsoOfVertexIso d' c' (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitConeIso d' c' hd' hc')).postcomp F)

/-- κ-compact 性も、存在する各図式の一つの元の余極限余錐で判定できる。 -/
lemma isKappaCompact_of_exists [Quasicategory C] {x : C _⦋0⦌}
    (h : ∀ (I : SSet.{u}) [Quasicategory I] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ I]
      (D : (SSet.uliftFunctor.{v, u}).obj I ⟶ C), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit D →
        ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity x) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift c))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, v} κ x :=
  preservesKappaFilteredColimits_of_exists h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
