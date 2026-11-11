module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeFamilyEquivalenceLifting
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.VertexIsoLifting
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeColimitFunctorIso

/-!
概要：図式固定の底余錐の同型に沿って相対余極限を移す。
方針：余錐の族の同型を持ち上げ、余錐全体の同型による相対余極限の保存を使う。
規約：元の図式と新しい像の余錐は厳密に保つ。
使われ方：標準底余錐上の局所存在を普遍 comma 底余錐上の局所存在へ移す。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：像の余錐と同型な指定底余錐の上にも相対余極限がある。
方針：固定図式の余錐の族の後合成で同型を持ち上げ、相対普遍性を移す。
規約：同型は図式固定の余錐の族の中で指定する。
使われ方：底余錐を標準形と普遍 comma 形の間で取り替える。 -/
lemma exists_kanRelativeColimit_over_iso_image {K D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (p : K ⟶ D) (U : D ⟶ E)
    (hU : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting U) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone U c)
    (b : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (p ≫ U))
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFamilyVertexEquiv (p ≫ U) b)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFamilyVertexEquiv (p ≫ U) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone U c))) :
    ∃ d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone U d ∧ d.val ≫ U = b.val := by
  have : InnerFibration U := hU.innerFibration
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanCoconeFamilyPostcomp p U
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFamilyVertexEquiv (p ≫ U) b)
      (q.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFamilyVertexEquiv p c)) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanCoconeFamilyPostcomp_vertex]
    exact e
  obtain ⟨v, hv, ⟨ev⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_kanVertexIso_lift_target q
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFamilyPostcomp_equivalenceLifting p U hU) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFamilyVertexEquiv p c)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFamilyVertexEquiv (p ≫ U) b) he
  obtain ⟨d, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFamilyVertexEquiv p).surjective v
  have hv' : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone U d = b := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFamilyVertexEquiv (p ≫ U)).injective
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanCoconeFamilyPostcomp_vertex]
    exact hv
  have ei : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso d.val c.val :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map ev (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K D) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p))
  exact ⟨d, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_of_functorIso U hc ei.symm,
    congrArg Subtype.val hv'⟩

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
