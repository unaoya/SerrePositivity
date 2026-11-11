module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteCoherentProductNativeCone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeReindexRestrictions
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.DiscreteCoherentSpaceProducts
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.DiscreteIndexIso

/-!
概要：元の有限 coherent 積の余極限頂点の native 積錐を一般の非空有限添字へ移す。
方針：指定全単射の元の形状同型で全錐を引き戻し、全頂点で元の図式と厳密に照合する。
規約：元の余極限頂点と各脚の全一単体を保持する。
使われ方：P_Σ の sifted 閉性で使う任意の有限離散極限錐との比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable (n : ℕ) {B : SSet.{u}}
  (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}))
  {J : Type u} (e : J ≃ ULift.{u} (Fin (n + 1)))

/-- 元の各余極限 Kan 対象を、指定された元の離散添字で表示する。 -/
def reindexedFiniteProductDiagram : Discrete J ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  Discrete.functor (fun j ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject (F (e j).down))

/-- 元の全単射による図式の前合成は、元の各因子を再添字した全図式そのもの。 -/
lemma reindexedFiniteProductDiagram_eq :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.liftedDiscreteIndexIso e).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductDiagram n
        (fun i ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject (F i))) =
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (reindexedFiniteProductDiagram n F e) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.liftedDiscreteDiagram_ext
  intro j
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductDiagram n
    (fun i ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject (F i)))).app _
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.liftedDiscreteIndexIso e).hom.app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex j))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.liftedDiscreteIndexIso_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve_vertex,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve_vertex]
  rfl

/-- 元の有限 coherent 積の余極限頂点を持つ、指定一般添字での native 積錐。 -/
def reindexedFiniteProductNativeCone [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity B] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (reindexedFiniteProductDiagram n F e)) :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSiftedCoherentProductNativeCone n F).reindexIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.liftedDiscreteIndexIso e)).cast
    (reindexedFiniteProductDiagram_eq n F e)

/-- 元の全錐の再添字は、同じ元の余極限頂点での有限積錐。 -/
lemma reindexedFiniteProductNativeCone_isLimit [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity B] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (reindexedFiniteProductNativeCone n F e) :=
  ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isLimitCone_iff_reindexIso _ _).mp (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSiftedCoherentProductNativeCone_isLimit n F)).cast _

/-- 再添字した元の全錐の頂点は元の coherent 余極限頂点そのもの。 -/
lemma reindexedFiniteProductNativeCone_vertex [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity B] :
    (reindexedFiniteProductNativeCone n F e).vertex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n F)) := by
  rw [reindexedFiniteProductNativeCone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_cast, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.joinCone_reindexIso_vertex,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSiftedCoherentProductNativeCone_vertex]

/-- 再添字した各 native 脚は、指定された元の脚と同じ全一単体。 -/
lemma reindexedFiniteProductNativeCone_leg_edge [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity B] (j : Discrete J) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (reindexedFiniteProductNativeCone n F e)
      (ULift.up (ComposableArrows.mk₀ j))).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSiftedCoherentProductNativeCone n F)
          (ULift.up (ComposableArrows.mk₀ (Discrete.mk (e j.as))))).edge := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSiftedCoherentProductNativeCone n F).reindexIso
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.liftedDiscreteIndexIso e)) _).edge = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nativeConeLeg_reindexIso_edge]
  rfl

/-- 元の添字族を全単射で一旦標準添字に移して戻すと、元の全図式を厳密に回収する。 -/
lemma reindexedFiniteProductDiagram_original
    (G : J → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (reindexedFiniteProductDiagram n
      (fun i ↦ G (e.symm (ULift.up i))) e) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (Discrete.functor (fun j ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject
          (G j))) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.liftedDiscreteDiagram_ext
  intro j
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve_vertex]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject
    (G (e.symm (ULift.up (e j.as).down)))) = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex _
  rw [ULift.up_down, e.symm_apply_apply]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
