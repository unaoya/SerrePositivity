module

public import SerrePositivity.InfinityCategories.F1B.Cones.CoconeFamilyDiagramEq
public import SerrePositivity.InfinityCategories.Core.CatInfinity.CoconeValEquality
public import SerrePositivity.InfinityCategories.F2.Ind.CofinalCoconeRestriction
public import SerrePositivity.InfinityCategories.F2.Ind.CofinalUniverseLift
public import SerrePositivity.InfinityCategories.F2.Presentable.SequentialEvenFaceComparison
public import SerrePositivity.InfinityCategories.F2.Presentable.SequentialColimitComparison
public import SerrePositivity.InfinityCategories.F2.Presentable.AlternatingOddSubsequenceComparison

/-!
概要：元の部分表示の全余錐を、同じ全図式の共終部分列の余錐として比較する。
方針：公開の余錐輸送と cofinal な制限を使い、全余錐の値と頂点を保持する。
規約：元の指定余極限を選び直さない。使われ方：二表示の共通小部分余極限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits

/-- 元の全余錐を、等しい共終制限図式の余錐へ同じ値のまま移す。 -/
def cofinalDiagramCocone {J K X : SSet.{u}} (p : J ⟶ K)
    {D : K ⟶ X} {E : J ⟶ X} (h : p ≫ D = E) (c : JoinCocone D) : JoinCocone E :=
  F1B.coconeOfDiagramEq h (c.restrict p)

/-- 同じ元の余錐頂点を厳密に保持する。 -/
lemma cofinalDiagramCocone_vertex {J K X : SSet.{u}} (p : J ⟶ K)
    {D : K ⟶ X} {E : J ⟶ X} (h : p ≫ D = E) (c : JoinCocone D) :
    (cofinalDiagramCocone p h c).vertex = c.vertex :=
  JoinCocone.vertex_restrict c p

/-- 共終性が与えられれば、この同じ全余錐は余極限である。 -/
lemma cofinalDiagramCocone_isColimit {J K X : SSet.{u}} [Quasicategory K] [Quasicategory X]
    (p : J ⟶ K) (hp : IsRightCofinal p) {D : K ⟶ X} {E : J ⟶ X}
    (h : p ≫ D = E) (c : JoinCocone D) (hc : IsColimitCone c) :
    IsColimitCone (cofinalDiagramCocone p h c) :=
  (isColimitCone_iff_of_cocone_val_eq (c.restrict p) (cofinalDiagramCocone p h c) rfl).mp
    ((Ind.isColimitCone_iff_restrict_rightCofinal p hp c).mp hc)

/-- 二つの部分表示が全比較の両共終部分列になれば、指定余極限の頂点は同型である。 -/
lemma nonempty_twoCofinalPresentation_colimitIso
    {X : SSet.{u + 1}} [Quasicategory X] (hX : HasSmallColimits X)
    {P₀ P₁ : SSet.{u}} [Quasicategory P₀] [Quasicategory P₁]
    (r₀ : nerve (ULift.{u} ℕ) ⟶ P₀) (hr₀ : IsRightCofinal r₀)
    (r₁ : nerve (ULift.{u} ℕ) ⟶ P₁) (hr₁ : IsRightCofinal r₁)
    (E₀ : (SSet.uliftFunctor.{u + 1, u}).obj P₀ ⟶ X)
    (E₁ : (SSet.uliftFunctor.{u + 1, u}).obj P₁ ⟶ X)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) ⟶ X)
    (h₀ : (SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (sequentialSubsequenceFunctor.{u} (fun n ↦ 2 * n) alternatingEven_monotone)) ≫ F =
      (SSet.uliftFunctor.{u + 1, u}).map r₀ ≫ E₀)
    (h₁ : (SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (sequentialSubsequenceFunctor.{u} (fun n ↦ 2 * n + 1) alternatingOdd_monotone)) ≫ F =
      (SSet.uliftFunctor.{u + 1, u}).map r₁ ≫ E₁)
    (c₀ : JoinCocone E₀) (hc₀ : IsColimitCone c₀)
    (c₁ : JoinCocone E₁) (hc₁ : IsColimitCone c₁) :
    Nonempty (VertexIso c₀.vertex c₁.vertex) := by
  let p₀ := (SSet.uliftFunctor.{u + 1, u}).map r₀
  let p₁ := (SSet.uliftFunctor.{u + 1, u}).map r₁
  let d₀ := cofinalDiagramCocone p₀ h₀.symm c₀
  let d₁ := cofinalDiagramCocone p₁ h₁.symm c₁
  have hd₀ := cofinalDiagramCocone_isColimit p₀ (Ind.isRightCofinal_ulift r₀ hr₀) h₀.symm c₀ hc₀
  have hd₁ := cofinalDiagramCocone_isColimit p₁ (Ind.isRightCofinal_ulift r₁ hr₁) h₁.symm c₁ hc₁
  obtain ⟨e⟩ := nonempty_subsequenceColimitVertexIso
    (fun n ↦ 2 * n) (fun n ↦ 2 * n + 1) alternatingEven_monotone alternatingOdd_monotone
    (fun k ↦ ⟨k, by change k ≤ 2 * k; omega⟩)
    (fun k ↦ ⟨k, by change k ≤ 2 * k + 1; omega⟩) hX d₀ hd₀ d₁ hd₁
  have hv₀ := cofinalDiagramCocone_vertex p₀ h₀.symm c₀
  have hv₁ := cofinalDiagramCocone_vertex p₁ h₁.symm c₁
  change d₀.vertex = c₀.vertex at hv₀
  change d₁.vertex = c₁.vertex at hv₁
  rw [hv₀, hv₁] at e
  exact ⟨e⟩

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
