module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ComparisonPrefixFactor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinPrismFixed

/-!
概要：compact な全図式に compact 頂点の余錐を加えても全頂点の compact 性を保つ。
方針：join の各頂点を元の図式か追加頂点へ分ける。
規約：全図式と元の指定余錐を保持する。使われ方：比較状態の後続形状の compact 性。

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


/-- 元の図式の全頂点と余錐頂点の compact 性は、全余錐図式の全頂点を覆う。 -/
lemma coconeVertices_compact {κ : Cardinal.{u}} {K C : SSet.{u + 1}} [Quasicategory C]
    {p : K ⟶ C} (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p)
    (hp : ∀ v, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (p.app _ v))
    (hw : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ w.vertex) :
    ∀ v, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (w.val.app _ v) := by
  intro v
  obtain ⟨a, rfl⟩ | ⟨b, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join_vertex_cases K Δ[0] v
  · have he := congrArg (fun F : K ⟶ C ↦ F.app (Opposite.op ⦋0⦌) a) w.property
    change w.val.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0]).app _ a) = p.app _ a at he
    rw [he]
    exact hp a
  · have hb : b = SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u + 1})) := by
      apply SSet.stdSimplex.ext
      intro i
      exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm
    subst b
    have he : w.val.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K Δ[0]).app _
        (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u + 1})))) = w.vertex := rfl
    rw [he]
    exact hw

/-- 後続因子化で得る全余錐の全頂点は、元の同じ compact 濃度を保持する。 -/
lemma ComparisonLeftFactor.cocone_compact {μ : Cardinal.{u}}
    {C : SSet.{u + 1}} [Quasicategory C] {I₀ I₁ : SSet.{u}}
    {D₀ : (SSet.uliftFunctor.{u + 1, u}).obj I₀ ⟶ C}
    {D₁ : (SSet.uliftFunctor.{u + 1, u}).obj I₁ ⟶ C}
    {c₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D₀} {c₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D₁}
    {s : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompactPresentationComparison μ D₀ D₁ c₀ c₁} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ComparisonLeftFactor s)
    (hD : ∀ i : I₀ _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (D₀.app _ (ULift.up i))) :
    ∀ v, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (f.cocone.val.app _ v) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coconeVertices_compact f.cocone s.compact (f.compact hD)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
