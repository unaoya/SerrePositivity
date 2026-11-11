module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FullyFaithfulColimitCreation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LimitColimitOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.MappingOpposite
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.OppositeFunctorIso

/-!
概要：充満忠実な像の極限頂点が元の像と同型なら元の極限が存在する。
方針：元の全錐を反転して余極限の存在構成へ渡す。
規約：同じ全図式と指定された頂点の像条件を保持する。
使われ方：全 Hom 族の表現可能な極限からの局所 Kan 余極限。

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


/-- 概要：充満忠実な像の元の指定極限の頂点が像と同型なら元の極限が存在する。
方針：元の反転全余錐の頂点と同じ反転同型を用いる。
規約：元の任意の形状を保持する。
使われ方：Hom 係数族による局所余極限の存在判定。 -/
lemma hasLimit_of_fullyFaithful_image_limit_iso
    {K A B : SSet.{u}} [Quasicategory A] [Quasicategory B]
    (F : A ⟶ B) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful F) (p : K ⟶ A)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (p ≫ F)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c)
    (hvertex : ∃ a : A _⦋0⦌, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
      (F.app (Opposite.op ⦋0⦌) a) c.vertex)) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit p := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanHasLimit_iff_hasColimit_op p).mpr
  let d := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq (SSet.opFunctor.map_comp p F) c.reverseCocone
  have hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d :=
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_isColimit_iff (SSet.opFunctor.map_comp p F) c.reverseCocone).mp
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_iff_reverseCocone c).mp hc)
  have hFop : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (SSet.opFunctor.map F) := by
    intro x y
    obtain ⟨x, rfl⟩ := SSet.opObjEquiv.symm.surjective x
    obtain ⟨y, rfl⟩ := SSet.opObjEquiv.symm.surjective y
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pinchedHomMap_equivalence_iff_op F y x).mp (hF y x)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.hasColimit_of_fullyFaithful_image_colimit_iso (SSet.opFunctor.map F)
    hFop (SSet.opFunctor.map p) d hd
  obtain ⟨a, ⟨e⟩⟩ := hvertex
  refine ⟨SSet.opObjEquiv.symm a, ⟨?_⟩⟩
  have hv : d.vertex = SSet.opObjEquiv.symm c.vertex := c.reverseCocone_vertex
  exact e.op ≪≫ (eqToIso (congrArg HomotopyCategory.mk hv)).symm

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
