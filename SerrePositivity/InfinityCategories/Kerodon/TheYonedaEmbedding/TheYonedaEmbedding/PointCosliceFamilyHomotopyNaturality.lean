module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerHom
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyRepresentative
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.EnrichedPrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.EnrichedPostcomposition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CosliceCoconeFamilyEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PointCosliceFamilyHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceUniversalPrism
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
/-! 指定coslice普遍円柱の制限と、全パラメータの可逆自然変換に沿う自然性。 -/

@[expose] public section
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 同じ普遍円柱の任意の族への厳密な制限。 -/
lemma pointCosliceFamilyHomotopy_precomp_h {A C : SSet.{u}} (c : C _⦋0⦌)
    (a : A ⟶ sliceUnder (yonedaEquiv.symm c)) :
    (a ▷ (Δ[1] : SSet.{u})) ≫ (pointCosliceFamilyHomotopy (𝟙 (sliceUnder (yonedaEquiv.symm c)))).h =
      (pointCosliceFamilyHomotopy a).h := by
  change (a ▷ (Δ[1] : SSet.{u})) ≫
    (β_ (sliceUnder (yonedaEquiv.symm c)) (Δ[1] : SSet.{u})).hom ≫ cosliceUniversalPrism c =
      (β_ A (Δ[1] : SSet.{u})).hom ≫ leftMappingSpacePrism A ≫ sliceUnderUncurry a
  rw [BraidedCategory.braiding_naturality_left_assoc, cosliceUniversalPrism_precomp]
/-- 同じ制限を全関手圏の射として照合する。 -/
lemma pointCosliceFamilyHomotopy_precomp_arrow {A C : SSet.{u}} (c : C _⦋0⦌)
    (a : A ⟶ sliceUnder (yonedaEquiv.symm c)) :
    Arrow.mk ((hoFunctor.map ((pre a).app C)).toFunctor.map
      (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (pointCosliceFamilyHomotopy (𝟙 (sliceUnder (yonedaEquiv.symm c))))))) =
      Arrow.mk (Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (pointCosliceFamilyHomotopy a))) := by
  rw [← functorHomotopyPrecomp_hom]
  apply Truncated.HomotopyCategory.congr_arrowMk_homMk
  change yonedaEquiv (curry ((a ▷ (Δ[1] : SSet.{u})) ≫
    (pointCosliceFamilyHomotopy (𝟙 (sliceUnder (yonedaEquiv.symm c)))).h)) =
      yonedaEquiv (curry (pointCosliceFamilyHomotopy a).h)
  rw [pointCosliceFamilyHomotopy_precomp_h]
private def cosliceCoefficientPost {K J C : SSet.{u}} {a b : K ⟶ J}
    (p : J ⟶ C) (α : FunctorHom a b) : FunctorHom (a ≫ p) (b ≫ p) :=
  (hoFunctor.map ((ihom K).map p)).toFunctor.map α
private def cosliceCoefficientPre {K J C : SSet.{u}} {p q : J ⟶ C}
    (a : K ⟶ J) (β : FunctorHom p q) : FunctorHom (a ≫ p) (a ≫ q) :=
  (hoFunctor.map ((pre a).app C)).toFunctor.map β

private lemma samePointCosliceUnitWhiskerNaturality {K C : SSet.{u}} [Quasicategory K] [Quasicategory C]
    (c : C _⦋0⦌) {a b : K ⟶ sliceUnder (yonedaEquiv.symm c)} (α : FunctorHom a b) :
    let J := sliceUnder (yonedaEquiv.symm c)
    let β : FunctorHom (SSet.const c : J ⟶ C) (sliceUnderProjection (yonedaEquiv.symm c)) :=
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (pointCosliceFamilyHomotopy (𝟙 J)))
    cosliceCoefficientPost (SSet.const c : J ⟶ C) α ≫ cosliceCoefficientPre b β =
      cosliceCoefficientPre a β ≫ cosliceCoefficientPost (sliceUnderProjection (yonedaEquiv.symm c)) α := by
  dsimp only
  let p := sliceUnderProjection (yonedaEquiv.symm c)
  let q := (SSet.const c : sliceUnder (yonedaEquiv.symm c) ⟶ C)
  let αc := (qcatCellEquiv a b).symm α
  let βc := (qcatCellEquiv q p).symm
    (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (pointCosliceFamilyHomotopy (𝟙 (sliceUnder (yonedaEquiv.symm c))))))
  have h := congrArg (qcatCellEquiv (a ≫ q) (b ≫ p)) (Bicategory.whisker_exchange αc βc).symm
  change qcatCellEquiv _ _ (Bicategory.whiskerRight αc (qcatMap q)) ≫
    qcatCellEquiv _ _ (Bicategory.whiskerLeft (qcatMap b) βc) =
      qcatCellEquiv _ _ (Bicategory.whiskerLeft (qcatMap a) βc) ≫
        qcatCellEquiv _ _ (Bicategory.whiskerRight αc (qcatMap p)) at h
  rw [qcatCell_whiskerRight, qcatCell_whiskerLeft, qcatCell_whiskerLeft,
    qcatCell_whiskerRight] at h
  simpa only [αc, βc, Equiv.apply_symm_apply, p, q, cosliceCoefficientPost, cosliceCoefficientPre] using h
private lemma cosliceCoefficientPostConstArrow {K J C : SSet.{u}} [Quasicategory J]
    {a b : K ⟶ J} (α : FunctorHom a b) (c : C _⦋0⦌) :
    Arrow.mk (cosliceCoefficientPost (SSet.const c : J ⟶ C) α) =
      Arrow.mk (𝟙 (HomotopyCategory.mk (functorVertex (SSet.const c : K ⟶ C)))) := by
  unfold cosliceCoefficientPost
  rw [← functorHomHomotopy_hom α, ← functorHomotopyPostcomp_hom]
  rw [← functorHomotopyRefl_hom (SSet.const c : K ⟶ C)]
  apply Truncated.HomotopyCategory.congr_arrowMk_homMk
  change yonedaEquiv (curry ((functorHomHomotopy α).h ≫ (SSet.const c : J ⟶ C))) =
    yonedaEquiv (curry (fst K (Δ[1] : SSet.{u}) ≫ (SSet.const c : K ⟶ C)))
  rw [SSet.comp_const, SSet.comp_const]
private lemma cosliceCompArrow {D : Type*} [Category* D] {a b c a' b' c' : D}
    (f : a ⟶ b) (g : b ⟶ c) (f' : a' ⟶ b') (g' : b' ⟶ c')
    (hf : Arrow.mk f = Arrow.mk f') (hg : Arrow.mk g = Arrow.mk g') :
    Arrow.mk (f ≫ g) = Arrow.mk (f' ≫ g') := by
  obtain ⟨ha, hb, hf⟩ := (Arrow.mk_eq_mk_iff f f').mp hf
  obtain ⟨_, hc, hg⟩ := (Arrow.mk_eq_mk_iff g g').mp hg
  cases ha
  cases hb
  cases hc
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf hg
  cases hf
  cases hg
  rfl
private lemma samePointCosliceUnitNaturalityArrow {K C : SSet.{u}} [Quasicategory K] [Quasicategory C]
    (c : C _⦋0⦌) {a b : K ⟶ sliceUnder (yonedaEquiv.symm c)} (e : FunctorIso a b) :
    Arrow.mk (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (pointCosliceFamilyHomotopy a)) ≫
      (e.postcomp (sliceUnderProjection (yonedaEquiv.symm c))).hom) =
      Arrow.mk (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (pointCosliceFamilyHomotopy b))) := by
  let p := sliceUnderProjection (yonedaEquiv.symm c)
  let q := (SSet.const c : sliceUnder (yonedaEquiv.symm c) ⟶ C)
  let β : FunctorHom q p := Truncated.HomotopyCategory.homMk
    (functorEdgeOfSimplicialHomotopy (pointCosliceFamilyHomotopy
      (𝟙 (sliceUnder (yonedaEquiv.symm c)))))
  have hp : cosliceCoefficientPost p e.hom = (e.postcomp p).hom :=
    (SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_hom e p).symm
  have ha := pointCosliceFamilyHomotopy_precomp_arrow c a
  have hb := pointCosliceFamilyHomotopy_precomp_arrow c b
  have hc := cosliceCoefficientPostConstArrow e.hom c
  have hL := cosliceCompArrow _ _ _ _ hc hb
  have hR := cosliceCompArrow _ _ _ _ ha (congrArg Arrow.mk hp)
  have hN := congrArg Arrow.mk (samePointCosliceUnitWhiskerNaturality c e.hom)
  have hL' : Arrow.mk (cosliceCoefficientPost q e.hom ≫ cosliceCoefficientPre b β) =
      Arrow.mk (Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (pointCosliceFamilyHomotopy b))) := by
    simpa only [Category.id_comp, q, β, cosliceCoefficientPre] using hL
  simp only [q, p, β, cosliceCoefficientPre] at hN hR hL'
  exact hR.symm.trans (hN.symm.trans hL')
/-- 同じ普遍円柱は、任意のパラメータ準圏からの可逆自然変換について自然。 -/
lemma pointCosliceFamilyHomotopy_naturality {K C : SSet.{u}} [Quasicategory K] [Quasicategory C]
    (c : C _⦋0⦌) {a b : K ⟶ sliceUnder (yonedaEquiv.symm c)} (e : FunctorIso a b) :
    Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (pointCosliceFamilyHomotopy a)) ≫
      (e.postcomp (sliceUnderProjection (yonedaEquiv.symm c))).hom =
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (pointCosliceFamilyHomotopy b)) :=
  (Arrow.mk_inj _ _).mp (samePointCosliceUnitNaturalityArrow c e)
end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
end
