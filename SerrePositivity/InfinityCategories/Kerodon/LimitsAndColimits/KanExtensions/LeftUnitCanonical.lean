module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftUnitInvertible
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCommaCoconeColimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCanonicalHom
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinPrismFixed

/-!
概要：可逆な指定単位を持つ左 Kan 拡張を標準局所余錐の条件へ移す。
方針：局所輸送の底と頂点での可逆性を全頂点へ移し、余錐全体の同型で余極限を輸送する。
規約：元の標準余錐そのものの余極限性を結論する。
使われ方：元の図式を厳密に保つ左 Kan 関手の構成。

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

/-- 概要：指定単位が可逆なら局所余錐の輸送も全体として可逆。
方針：底での成分を指定単位へ、頂点での成分を固定条件へ移し、join の全頂点を検査する。
規約：標的 D だけを quasicategory とする。
使われ方：輸送後の余極限を標準余錐へ戻す。 -/
lemma kanLeftTransport_isIso_of_unit_isIso {K C D : SSet.{u}} [Quasicategory D]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D} {β : SSet.Homotopy F₀ (δ ≫ F)}
    {c : C _⦋0⦌} (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanCoconeTransport δ F₀ F β c)
    (hβ : IsIso (SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β))) :
    IsIso (SSet.Truncated.HomotopyCategory.homMk t.edge) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isInvertibleEdge_iff_evaluateFunctorAt t.edge).2
  intro v
  obtain ⟨a, rfl⟩ | ⟨b, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join_vertex_cases (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c) Δ[0] v
  · have he : IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (SSet.Truncated.HomotopyCategory.homMk t.edge)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c) (Δ[0] : SSet.{u})).app (Opposite.op ⦋0⦌) a)) := by
      apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftTransport_source_component_isIso_iff t a).2
      have := hβ
      infer_instance
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomEvaluate_isIso_iff
      (SSet.Truncated.HomotopyCategory.homMk t.edge) _).1 he
  · have hb : b = stdSimplex.obj₀Equiv.symm (0 : Fin 1) := by
      apply stdSimplex.obj₀Equiv.injective
      rw [Equiv.apply_symm_apply]
      apply Fin.ext
      have := (stdSimplex.obj₀Equiv b).isLt
      change (stdSimplex.obj₀Equiv b).val = 0
      omega
    subst b
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftTransport_apex_isIso t

/-- 概要：可逆な単位を持つ左 Kan 拡張は標準局所余錐も余極限。
方針：輸送の同型で輸送後の余極限性を標準余錐へ移す。
規約：指定単位の類の可逆性を明示する。
使われ方：左 Kan 関手の元の関手圏内の頂点条件の構成。 -/
lemma kanLeftKanExtension_canonicalColimits_of_unit_isIso {K C D : SSet.{u}}
    [Quasicategory D] (δ : K ⟶ C) {F₀ : K ⟶ D} {F : C ⟶ D}
    (β : SSet.Homotopy F₀ (δ ≫ F)) (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension δ F₀ F β)
    (hi : IsIso (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β))) :
    ∀ c : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ F c) := by
  intro c
  obtain ⟨t, ht⟩ := hβ c
  have := kanLeftTransport_isIso_of_unit_isIso t hi
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsColimitCone_of_functorIso ht (asIso (SSet.Truncated.HomotopyCategory.homMk t.edge))

/-- 概要：元の標準左 Kan 条件は関手圏全体の同型で保たれる。
方針：標準局所余錐を与える射への前合成で同型を移し、余錐全体の余極限性を輸送する。
規約：単に点ごとの値の同型を仮定しない。
使われ方：単射上で同型を延長した後の厳密な関手の Kan 条件。 -/
lemma kanLeftCanonicalColimits_of_functorIso {K C D : SSet.{u}} [Quasicategory D]
    (δ : K ⟶ C) {F G : C ⟶ D} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G)
    (hF : ∀ c : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ F c)) :
    ∀ c : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ G c) := by
  intro c
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsColimitCone_of_functorIso (hF c) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp e (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonicalCoconeMap δ c))

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
