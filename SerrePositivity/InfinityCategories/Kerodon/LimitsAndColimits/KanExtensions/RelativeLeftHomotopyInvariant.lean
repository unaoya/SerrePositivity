module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeLeftExtension
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftHomotopyInvariant

/-!
概要：相対左 Kan 条件の指定変換のホモトピー類による不変性。
方針：比較余錐の反転同型を全余錐の同型へ戻し、標準 U 余極限性を移す。
規約：関手の両端は固定し、指定変換の h Fun の類だけを比較する。
使われ方：指定変換の類を保つ相対 join 厳密化の局所判定。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：同じ h Fun の類を持つ指定変換の比較余錐は同じ U 余極限性を持つ。
方針：輸送の反転した族の同型を全余錐の関手同型へ写す。
規約：指定した二つの輸送の余錐自体を比較する。
使われ方：相対左 Kan 条件の h 不変性。 -/
lemma kanLeftTransport_isRelativeColimit_iff_of_homMk_eq {K C D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) [InnerFibration U]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {α β : SSet.Homotopy F₀ (δ ≫ F)} {c : C _⦋0⦌}
    (h : SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy α) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β))
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanCoconeTransport δ F₀ F α c) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanCoconeTransport δ F₀ F β c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone U t.cocone ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone U s.cocone := by
  obtain ⟨e⟩ := t.coconeFamily_opIso_of_homMk_eq h s
  have e' := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanVertexIso_unop e
  have e'' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso t.cocone.val s.cocone.val :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e' (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c) D)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram δ F₀ c)))
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_iff_of_functorIso U _ _ e''

/-- 概要：指定変換の h Fun の類が等しければ相対左 Kan 条件は同値。
方針：一方の局所輸送を取り、他方の輸送へ比較余錐の相対普遍性を移す。
規約：元の図式と延長候補は変えない。
使われ方：厳密化による指定変換の類の保存を相対 Kan 条件へ反映する。 -/
lemma kanIsRelativeLeftKanExtension_iff_of_homMk_eq {K C D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) [InnerFibration U]
    (δ : K ⟶ C) (F₀ : K ⟶ D) (F : C ⟶ D)
    (α β : SSet.Homotopy F₀ (δ ≫ F))
    (h : SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy α) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeLeftKanExtension U δ F₀ F α ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeLeftKanExtension U δ F₀ F β := by
  have hforward (α β : SSet.Homotopy F₀ (δ ≫ F))
      (hh : SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy α) =
        SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β))
      (hα : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeLeftKanExtension U δ F₀ F α) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeLeftKanExtension U δ F₀ F β := by
    intro c
    obtain ⟨t, ht⟩ := hα c
    obtain ⟨s⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCoconeTransport_nonempty δ F₀ F β c
    exact ⟨s, (kanLeftTransport_isRelativeColimit_iff_of_homMk_eq U hh t s).1 ht⟩
  exact ⟨hforward α β h, hforward β α h.symm⟩

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
