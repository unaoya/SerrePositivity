module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeFamilyDiagramEq
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoconeValEquality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalCoconeRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.CofinalUniverseLift
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialEvenFaceComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialColimitComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AlternatingOddSubsequenceComparison

/-!
概要：元の部分表示の全余錐を、同じ全図式の共終部分列の余錐として比較する。
方針：公開の余錐輸送と cofinal な制限を使い、全余錐の値と頂点を保持する。
規約：元の指定余極限を選び直さない。使われ方：二表示の共通小部分余極限。

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


/-- 元の全余錐を、等しい共終制限図式の余錐へ同じ値のまま移す。 -/
def cofinalDiagramCocone {J K X : SSet.{u}} (p : J ⟶ K)
    {D : K ⟶ X} {E : J ⟶ X} (h : p ≫ D = E) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone E :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeOfDiagramEq h (c.restrict p)

/-- 同じ元の余錐頂点を厳密に保持する。 -/
lemma cofinalDiagramCocone_vertex {J K X : SSet.{u}} (p : J ⟶ K)
    {D : K ⟶ X} {E : J ⟶ X} (h : p ≫ D = E) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) :
    (cofinalDiagramCocone p h c).vertex = c.vertex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_restrict c p

/-- 共終性が与えられれば、この同じ全余錐は余極限である。 -/
lemma cofinalDiagramCocone_isColimit {J K X : SSet.{u}} [Quasicategory K] [Quasicategory X]
    (p : J ⟶ K) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal p) {D : K ⟶ X} {E : J ⟶ X}
    (h : p ≫ D = E) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (cofinalDiagramCocone p h c) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq (c.restrict p) (cofinalDiagramCocone p h c) rfl).mp
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isColimitCone_iff_restrict_rightCofinal p hp c).mp hc)

/-- 二つの部分表示が全比較の両共終部分列になれば、指定余極限の頂点は同型である。 -/
lemma nonempty_twoCofinalPresentation_colimitIso
    {X : SSet.{u + 1}} [Quasicategory X] (hX : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits X)
    {P₀ P₁ : SSet.{u}} [Quasicategory P₀] [Quasicategory P₁]
    (r₀ : nerve (ULift.{u} ℕ) ⟶ P₀) (hr₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal r₀)
    (r₁ : nerve (ULift.{u} ℕ) ⟶ P₁) (hr₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal r₁)
    (E₀ : (SSet.uliftFunctor.{u + 1, u}).obj P₀ ⟶ X)
    (E₁ : (SSet.uliftFunctor.{u + 1, u}).obj P₁ ⟶ X)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) ⟶ X)
    (h₀ : (SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSubsequenceFunctor.{u} (fun n ↦ 2 * n) _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingEven_monotone)) ≫ F =
      (SSet.uliftFunctor.{u + 1, u}).map r₀ ≫ E₀)
    (h₁ : (SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSubsequenceFunctor.{u} (fun n ↦ 2 * n + 1) _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingOdd_monotone)) ≫ F =
      (SSet.uliftFunctor.{u + 1, u}).map r₁ ≫ E₁)
    (c₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone E₀) (hc₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c₀)
    (c₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone E₁) (hc₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c₁) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso c₀.vertex c₁.vertex) := by
  let p₀ := (SSet.uliftFunctor.{u + 1, u}).map r₀
  let p₁ := (SSet.uliftFunctor.{u + 1, u}).map r₁
  let d₀ := cofinalDiagramCocone p₀ h₀.symm c₀
  let d₁ := cofinalDiagramCocone p₁ h₁.symm c₁
  have hd₀ := cofinalDiagramCocone_isColimit p₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isRightCofinal_ulift r₀ hr₀) h₀.symm c₀ hc₀
  have hd₁ := cofinalDiagramCocone_isColimit p₁ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isRightCofinal_ulift r₁ hr₁) h₁.symm c₁ hc₁
  obtain ⟨e⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nonempty_subsequenceColimitVertexIso
    (fun n ↦ 2 * n) (fun n ↦ 2 * n + 1) _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingEven_monotone _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingOdd_monotone
    (fun k ↦ ⟨k, by change k ≤ 2 * k; omega⟩)
    (fun k ↦ ⟨k, by change k ≤ 2 * k + 1; omega⟩) hX d₀ hd₀ d₁ hd₁
  have hv₀ := cofinalDiagramCocone_vertex p₀ h₀.symm c₀
  have hv₁ := cofinalDiagramCocone_vertex p₁ h₁.symm c₁
  change d₀.vertex = c₀.vertex at hv₀
  change d₁.vertex = c₁.vertex at hv₁
  rw [hv₀, hv₁] at e
  exact ⟨e⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
