module

public import SerrePositivity.InfinityCategories.F2.Presentable.FullyFaithfulHomComparison
public import SerrePositivity.InfinityCategories.F2.Presentable.EquivalenceColimits
public import SerrePositivity.InfinityCategories.Core.Compact.UniverseCoconePostcomposition
public import SerrePositivity.InfinityCategories.F2.Compact.RepresentableRetractions

/-!
概要：κ-compact 性は、元の同値と同じ小さい κ-filtered 全余錐によって輸送できる。
方針：充満忠実関手の全 Hom 同型で反映し、逆同値と元の合成同型で保存も得る。
規約：元の全共変 Hom の定義と添字の宇宙を保持。compact 性を追加仮定に隠さない。
使われ方：κ-accessible 圏の compact 生成族の同値による輸送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- κ-filtered 余極限を保つ充満忠実関手は、元の像の κ-compact 性を反映する。 -/
lemma isKappaCompact_of_fullyFaithful_image {κ : Cardinal.{u}}
    {C E : SSet.{u + 1}} [Quasicategory C] [Quasicategory E]
    (G : C ⟶ E) (hG : IsFullyFaithful G) (hp : IsKappaAccessibleFunctor κ G)
    (x : C _⦋0⦌) (hx : Compact.IsKappaCompact.{u, u + 1} κ (G.app (Opposite.op ⦋0⦌) x)) :
    Compact.IsKappaCompact.{u, u + 1} κ x := by
  intro I hI hκ D c hc
  have h : IsColimitCone (mapJoinCocone
      ((SSet.uliftFunctor.{u + 2, u + 1}).map G ≫
        covariantRepresentableInfinity (G.app (Opposite.op ⦋0⦌) x)) (JoinCocone.ulift c)) := by
    rw [Compact.mapJoinCocone_universe_comp]
    exact hx I (D ≫ G) (mapJoinCocone G c) (hp I D c hc)
  exact h.of_functorIso ((covariantHomComparisonIso G hG x).precomp
    (JoinCocone.ulift c).val).symm

/-- 元の同値の同じ対象像は、元の対象の κ-compact 性を保持する。 -/
lemma isKappaCompact_image_of_equivalence {κ : Cardinal.{u}}
    {C E : SSet.{u + 1}} [Quasicategory C] [Quasicategory E]
    (e : QCatEquivalence C E) (x : C _⦋0⦌) (hx : Compact.IsKappaCompact.{u, u + 1} κ x) :
    Compact.IsKappaCompact.{u, u + 1} κ (e.hom.app (Opposite.op ⦋0⦌) x) := by
  have h := (Compact.isKappaCompact_iff_of_iso (κ := κ) (e.homInvIso.app x)).mpr hx
  exact isKappaCompact_of_fullyFaithful_image e.inv e.symm.isQCatEquivalence.isFullyFaithful
    (equivalence_preservesSmallKappaFilteredColimits κ e.symm.isQCatEquivalence) _ h

/-- 元の同値は、同じ指定対象の κ-compact 性を保存・反映する。 -/
lemma isKappaCompact_iff_equivalence {κ : Cardinal.{u}}
    {C E : SSet.{u + 1}} [Quasicategory C] [Quasicategory E]
    (e : QCatEquivalence C E) (x : C _⦋0⦌) :
    Compact.IsKappaCompact.{u, u + 1} κ x ↔
      Compact.IsKappaCompact.{u, u + 1} κ (e.hom.app (Opposite.op ⦋0⦌) x) :=
  ⟨isKappaCompact_image_of_equivalence e x,
    isKappaCompact_of_fullyFaithful_image e.hom e.isQCatEquivalence.isFullyFaithful
      (equivalence_preservesSmallKappaFilteredColimits κ e.isQCatEquivalence) x⟩

end SerrePositivity.InfinityCategories.F2.Presentable
