module

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.VerdierRelativeConeRecovery
public import SerrePositivity.KST.LocalizingInvariants.VerdierInitialConeTensorRelativeGluing
public import SerrePositivity.KST.LocalizingInvariants.InitialConeTensorBoundaryViews

/-!
概要：パラメータの尾部での相対商錐回収から、左錐全体での相対回収を構成する。
方針：尾部の実回収と元の全図式を貼り、同じ境界固定の比較を保持して実延長する。
規約：尾部の実図式・逆比較・共有円柱の一致を帰納仮定から実構成する。
使われ方：c5 の標準単体の次元帰納。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 有限パラメータへの左錐の追加は、元の有限境界を固定する商錐回収を保つ。 -/
lemma hasVerdierRelativeConeRecovery_join {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C} (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    (L : SSet.{u}) [L.Finite] (ih : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.HasVerdierRelativeConeRecovery q.hom L) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.HasVerdierRelativeConeRecovery q.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) L) := by
  intro K _ p H hb
  let j := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) K
  let l := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) L
  let pL := (K ◁ l) ≫ p
  let HL := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K ◁ l) ≫ H
  have hbL : (j ▷ L) ≫ HL = pL ≫ q.hom := by
    change (j ▷ L) ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K ◁ l) ≫ H) = _
    rw [← Category.assoc, ← whisker_exchange, Category.assoc, hb]
    rfl
  obtain ⟨d⟩ := ih K pL HL hbL
  have : Mono (j ▷ L) := (tensorRight L).map_mono j
  have hdq : (j ▷ L) ≫ (d.diagram ≫ q.hom) = pL ≫ q.hom := by
    rw [← Category.assoc, d.boundary]
  obtain ⟨V, hV, hiV⟩ := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.exists_relativeComparisonInverse (j ▷ L) (pL ≫ q.hom)
    (d.diagram ≫ q.hom) HL hdq hbL d.comparison d.fixed d.invertible
  let F := (initialConeTensorOldIso K L).hom ≫ p
  let G := (initialConeTensorTailIso K L).hom ≫ d.diagram
  have w : SSet.opFunctor.map (K.op ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl L.op (Δ[0] : SSet.{u})) ≫ F =
      SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K.op (Δ[0] : SSet.{u}) ▷ L.op) ≫ G := by
    change _ ≫ ((initialConeTensorOldIso K L).hom ≫ p) =
      _ ≫ ((initialConeTensorTailIso K L).hom ≫ d.diagram)
    rw [← Category.assoc, initialConeTensorOldIso_overlap, Category.assoc,
      ← Category.assoc (SSet.opFunctor.map _), initialConeTensorTailIso_overlap,
      Category.assoc, d.boundary]
  have hF : initialConeTensorOldInclusion K L ≫ initialConeTensorCornerInclusion K L ≫ H =
      F ≫ q.hom := by
    rw [← Category.assoc, initialConeTensorOldInclusion_view, Category.assoc, hb]
    rfl
  let J : SSet.Homotopy
      (initialConeTensorOldInclusion K L ≫ initialConeTensorCornerInclusion K L ≫ H)
      (F ≫ q.hom) := {
    h := fst _ (Δ[1] : SSet.{u}) ≫ (F ≫ q.hom)
    h₀ := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (F ≫ q.hom)).h₀.trans hF.symm
    h₁ := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (F ≫ q.hom)).h₁
    rel := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (F ≫ q.hom)).rel }
  let T : SSet.Homotopy
      (initialConeTensorTailInclusion K L ≫ initialConeTensorCornerInclusion K L ≫ H)
      (G ≫ q.hom) := {
    h := ((initialConeTensorTailIso K L).hom ▷ (Δ[1] : SSet.{u})) ≫ V.h
    h₀ := by
      rw [SSet.ι₀_comp_assoc, V.h₀]
      change (initialConeTensorTailIso K L).hom ≫ HL =
        initialConeTensorTailInclusion K L ≫ initialConeTensorCornerInclusion K L ≫ H
      rw [← Category.assoc (initialConeTensorTailInclusion K L),
        initialConeTensorTailInclusion_view]
      rfl
    h₁ := by rw [SSet.ι₁_comp_assoc, V.h₁]; rfl
    rel := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp V (initialConeTensorTailIso K L).hom).rel }
  have hiT : ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge T x).toTruncated := by
    intro x
    have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge T x).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
          (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp V (initialConeTensorTailIso K L).hom) x).edge := rfl
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.simplicialHomotopyVertexEdge_precomp_edge V (initialConeTensorTailIso K L).hom x)).mpr
        (hiV _)
  have hw : (SSet.opFunctor.map (K.op ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl L.op (Δ[0] : SSet.{u})) ▷ Δ[1]) ≫ J.h =
      (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K.op (Δ[0] : SSet.{u}) ▷ L.op) ▷ Δ[1]) ≫ T.h := by
    change _ ≫ (fst _ Δ[1] ≫ (F ≫ q.hom)) =
      _ ≫ (((initialConeTensorTailIso K L).hom ▷ Δ[1]) ≫ V.h)
    rw [← comp_whiskerRight_assoc, initialConeTensorTailIso_overlap, comp_whiskerRight]
    simp only [Category.assoc]
    rw [hV]
    have hf : (SSet.opFunctor.map (K.op ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl L.op (Δ[0] : SSet.{u})) ▷
        (Δ[1] : SSet.{u})) ≫ fst _ Δ[1] =
        fst _ Δ[1] ≫ SSet.opFunctor.map (K.op ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl L.op (Δ[0] : SSet.{u})) := rfl
    rw [← Category.assoc (SSet.opFunctor.map _ ▷ (Δ[1] : SSet.{u})), hf, Category.assoc]
    change fst _ Δ[1] ≫
      (SSet.opFunctor.map (K.op ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl L.op (Δ[0] : SSet.{u})) ≫
        (initialConeTensorOldIso K L).hom ≫ p ≫ q.hom) = _
    rw [← Category.assoc (SSet.opFunctor.map _), initialConeTensorOldIso_overlap,
      Category.assoc]
    have hf' : ((initialConeTensorOverlapIso K L).hom ▷ (Δ[1] : SSet.{u})) ≫
        fst (K ⊗ L) Δ[1] = fst _ Δ[1] ≫ (initialConeTensorOverlapIso K L).hom := rfl
    rw [← Category.assoc ((initialConeTensorOverlapIso K L).hom ▷ (Δ[1] : SSet.{u})),
      hf', Category.assoc]
    rfl
  obtain ⟨D, U, hD, _, hU, hiU⟩ := exists_verdierInitialConeTensorRelativeGluing
    h K L F G w H J T hw (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.relativeConeComparison_invertible_of_constant J rfl) hiT rfl
  have hD' : (j ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) L) ≫ D = p := by
    apply (cancel_epi (initialConeTensorOldIso K L).hom).mp
    rw [← Category.assoc, ← initialConeTensorOldInclusion_view]
    exact hD
  have hU' : ((j ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) L) ▷ (Δ[1] : SSet.{u})) ≫ U.h =
      fst (K ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) L) Δ[1] ≫ (p ≫ q.hom) := by
    apply (cancel_epi ((initialConeTensorOldIso K L).hom ▷ (Δ[1] : SSet.{u}))).mp
    rw [← comp_whiskerRight_assoc, ← initialConeTensorOldInclusion_view, hU]
    rfl
  exact ⟨⟨D, hD', U, hU', hiU⟩⟩

end SerrePositivity.KST.LocalizingInvariants
