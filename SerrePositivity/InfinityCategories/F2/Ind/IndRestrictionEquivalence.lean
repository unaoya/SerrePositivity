module

public import SerrePositivity.InfinityCategories.F2.Ind.IndLeftKanPreservation
public import SerrePositivity.InfinityCategories.F2.Ind.IndRestrictionFullyFaithful
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulEquivalence

/-!
概要：元の Yoneda 制限は κ-filtered 余極限を保つ関手の ∞ 圏の同値。
方針：保存する左 Kan 延長と指定単位の回収同型で本質的全射性を証明し、F0 の判定を使う。
規約：κ と C と小さい添字は宇宙 u、Indκ と D と関手空間は宇宙 u+1。
使われ方：HTT 5.3.5.10、Indκ の自由 κ-filtered 余極限完備化の普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の保存関手を、保存関手が張る全部分 ∞ 圏の頂点として読む。 -/
def kappaContinuousFunctorVertex (κ : Cardinal.{u}) {X D : SSet.{u + 1}}
    (G : X ⟶ D) (hG : PreservesSmallKappaFilteredColimits κ G) :
    (KappaContinuousFunctorInfinity κ X D) _⦋0⦌ :=
  ⟨functorVertex G, by
    intro v
    have hv : v = 𝟙 _ := Subsingleton.elim _ _
    subst v
    have hrec : (functorVertexEquiv X D).symm (functorVertex G) = G :=
      (functorVertexEquiv X D).symm_apply_apply G
    simpa only [op_id, CategoryTheory.Functor.map_id_apply, hrec] using hG⟩

variable (κ : Cardinal.{u}) [Fact κ.IsRegular] (C : SSet.{u}) [Quasicategory C]
  (D : SSet.{u + 1}) [Quasicategory D]

/-- 同じ小さい κ-filtered 余極限を持つ標的では、元の Yoneda 制限射自体が本質的全射。 -/
lemma indKappaContinuousRestriction_isEssentiallySurjective
    (hD : HasSmallKappaFilteredColimits κ D) :
    IsEssentiallySurjective (indKappaContinuousRestriction κ C D) := by
  intro v
  let F₀ := (functorVertexEquiv ((SSet.uliftFunctor.{u + 1, u}).obj C) D).symm v
  obtain ⟨G, β, hβ⟩ := ind_exists_leftKanExtension κ hD F₀
  have hG := indLeftKanExtension_preservesSmallKappaFilteredColimits κ β hβ
  refine ⟨kappaContinuousFunctorVertex κ G hG, ?_⟩
  have hv : functorVertex F₀ = v := (functorVertexEquiv _ _).apply_symm_apply v
  change Nonempty (VertexIso (functorVertex (indYoneda κ C ≫ G)) v)
  rw [← hv]
  exact ⟨indLeftKanExtensionRecoveryIso κ β hβ⟩

/-- HTT 5.3.5.10：元の Yoneda による制限写像そのものが ∞ 圏の同値。 -/
lemma indKappaContinuousRestriction_isQCatEquivalence
    (hD : HasSmallKappaFilteredColimits κ D) :
    IsQCatEquivalence (indKappaContinuousRestriction κ C D) :=
  isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    (indKappaContinuousRestriction_isFullyFaithful κ C D)
    (indKappaContinuousRestriction_isEssentiallySurjective κ C D hD)

/-- 同じ制限射を順射に持つ Fun^κ(Indκ(C),D) ≃ Fun(C,D) の同値データ。 -/
def indKappaContinuousRestrictionEquivalence (hD : HasSmallKappaFilteredColimits κ D) :
    QCatEquivalence (KappaContinuousFunctorInfinity κ (IndInfinity κ C) D)
      ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj C)).obj D) :=
  (indKappaContinuousRestriction_isQCatEquivalence κ C D hD).choose

/-- 同値の順射は、元の Yoneda による実際の制限写像に厳密に一致する。 -/
lemma indKappaContinuousRestrictionEquivalence_hom (hD : HasSmallKappaFilteredColimits κ D) :
    (indKappaContinuousRestrictionEquivalence κ C D hD).hom =
      indKappaContinuousRestriction κ C D := rfl

end SerrePositivity.InfinityCategories.F2.Ind
